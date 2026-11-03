import Solcore.Synthesis.Source.MemoryArrayCases
import Solcore.Synthesis.Source.ArrayAbiCases

/-! The `runtime-memory-arrays` and `runtime-array-abi` profiles. Their Core
references hold each array as a length cell and element cells, check every
index, slice bound, allocation and `pop` with Solidity's panic codes and a
narrow parameter's elements with std's `DirtyHigherBitsForInteger()`; they
agree with the plans' direct interpreter on generated plans, and four
fixtures' sources and results are golden, the results from the corpus
validator's separate Python model. Admission refuses names, operands, bounds,
parameters, results and raw values outside each profile; generation draws
every shape and replays exactly; tampering is refused, and reductions are
strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceArrayCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.Arrays (Profile Observed)

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

/-- The eight boundary inputs, then four more. -/
private def inputs : List Nat :=
  Solcore.Synthesis.Core.Integers.boundaryWords ++
    [3, 7, 2 ^ 128 + 5, 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef]

/-- A returned Word in decimal, return or revert data in hex. -/
private def observedText : Observed → String
  | .word word => toString word.val
  | .output data | .reverted data => Arrays.hexBytes data

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
  | .output bytes => Arrays.hexBytes bytes
  | .panic code => Arrays.hexBytes ([0x4e, 0x48, 0x7b, 0x71] ++ wordBytes code)
  | .dirty => "0x6cc54a63"

/-! Fixtures. The first memory array fixture is `int8`: an array made with
`new` at an input length, a literal and its alias written through the alias,
a slice of the literal seen after a write, a grid at a flagged length, a
checked sum through the alias, a loop with an unchecked product and a generic
read, and a read through the literal. The second is `uint256` over the storage
array: three pushes, a slice of it, `pop`, a read through the slice, then
`setLength`, a checked division of an element, a helper's array in a grid of
two rows and a checked `sc_inc` through a row. The ABI fixtures take a raw
`calldata<uint16[]>` and a clean `uint16[]` and return the second after a
write, with a copy, a read and a loop over the first; and a raw `int8[]` whose
slice by `sc_tail` is returned as a copy after a raw `sc_put` and a read
through a grid row holding it. -/

private def memoryA : Plan := {
  element := ⟨true, 1⟩, values := [⟨0, false⟩, ⟨128, false⟩, ⟨127, false⟩],
  indices := [⟨0, 3, false⟩, ⟨0, 7, true⟩], params := [], result := .word,
  steps := [.alloc (.input 0), .literal [.input 0, .input 1, .literal 0], .alias (.var 1),
    .act (.write (.array (.var 2)) (.literal 1) (.input 0) (.compound .add false)),
    .slice (.array (.var 1)) (.range (.literal 0) (.input 0)),
    .act (.write (.array (.var 1)) (.literal 0) (.input 1) .plain),
    .act (.observe (.element (.slice 0) (.literal 0))), .grid (.input 1), .act (.observe (.gridLength 0)),
    .act (.observe (.sum (.var 2))),
    .loop (.array (.var 0)) [.write (.array (.var 0)) .counter (.input 0) (.compound .mul true),
      .observe (.get (.array (.var 1)) .counter)],
    .act (.observe (.element (.array (.var 1)) (.literal 1)))]}

private def memoryB : Plan := {
  element := ⟨false, 32⟩, values := [⟨0, false⟩, ⟨1, false⟩], indices := [⟨8, 3, false⟩], params := [],
  result := .word,
  steps := [.push (.input 0), .push (.input 1), .push (.literal 4), .slice .storage (.start (.literal 1)), .pop,
    .act (.observe (.element (.slice 0) (.input 0))), .setLength (.literal 3),
    .act (.write .storage (.literal 0) (.input 1) (.compound .div false)), .made (.input 0) (.input 1),
    .gridOf [.var 0, .var 0], .act (.write (.row 0 (.input 0)) (.literal 1) (.input 0) .inc),
    .act (.observe (.element (.array (.var 0)) (.literal 1)))]}

private def abiA : Plan := {
  element := ⟨false, 2⟩, values := [⟨0, false⟩], indices := [⟨1, 3, false⟩],
  params := [⟨true, .input 0 3, 0, true⟩, ⟨false, .literal 2, 1, false⟩], result := .array (.param 1),
  steps := [.slice (.calldata 0) .all, .copy 0, .act (.write (.array (.param 1)) (.input 0) (.input 0) .plain),
    .act (.observe (.element (.calldata 0) (.input 0))), .loop (.calldata 0) [.observe (.element (.calldata 0) .counter)]]}

private def abiB : Plan := {
  element := ⟨true, 1⟩, values := [⟨0, true⟩, ⟨128, true⟩], indices := [],
  params := [⟨false, .literal 3, 0, true⟩], result := .copy 0,
  steps := [.tail (.param 0) (.literal 1), .act (.write (.array (.param 0)) (.literal 2) (.input 1) .put),
    .gridLiteral [[.input 0, .literal 7], [.input 0]], .setRow 0 (.literal 1) (.param 0),
    .act (.observe (.element (.row 0 (.literal 1)) (.literal 2)))]}

private def memoryASource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_sum(sc_v: int8[]) returns (int8) {\n    let sc_t: int8 = 0;\n    for (let sc_i: uint256 = 0; sc_i < sc_v.length; sc_i += 1) {\n        sc_t += sc_v[sc_i];\n    }\n    return sc_t;\n}\n\nfunction sc_get<c>(sc_c: c, sc_i: uint256) returns (int8) where (c, uint256): RValueIdxAccess<int8> {\n    return ridx(sc_c, sc_i);\n}\n\ncontract SynthesizedMemoryArrays {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: int8 = Typedef.abs(sc_signextend(0, sc_x));\n        let sc_v1: int8 = Typedef.abs(sc_signextend(0, (sc_x + 128)));\n        let sc_v2: int8 = Typedef.abs(sc_signextend(0, (sc_x + 127)));\n        let sc_k0: uint256 = uint256((sc_x & 3));\n        let sc_k1: uint256 = uint256((sc_x & 0x8000000000000000000000000000000000000000000000000000000000000007));\n        let sc_r: word = 0;\n        let sc_a0: int8[] = new int8[](sc_k0);\n        let sc_a1: int8[] = [sc_v0, sc_v1, (-128)];\n        let sc_a2: int8[] = sc_a1;\n        sc_a2[1] += sc_v0;\n        let sc_s0 = sc_a1[0:sc_k0];\n        sc_a1[0] = sc_v1;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_s0[uint256(0)]));\n        let sc_g0: int8[][] = new int8[][](sc_k1);\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_g0.length));\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_sum(sc_a2)));\n        for (let sc_i: uint256 = 0; sc_i < sc_a0.length; sc_i += 1) {\n            unchecked {\n                sc_a0[sc_i] *= sc_v0;\n            }\n            sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_get(sc_a1, sc_i)));\n        }\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_a1[1]));\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-memory-array-corpus.py`. -/
private def memoryAResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000041",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"]

private def memoryBSource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\nfunction sc_inc(sc_c: memref<uint256>, sc_w: uint256) {\n    CanStore.store(sc_c, (CanStore.load(sc_c) + sc_w));\n}\n\nfunction sc_mk(sc_p: uint256, sc_q: uint256) returns (uint256[]) {\n    return [sc_p, sc_q];\n}\n\ncontract SynthesizedMemoryArrays {\n    sc_st: uint256[];\n\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: uint256 = Typedef.abs(sc_x);\n        let sc_v1: uint256 = Typedef.abs((sc_x + 1));\n        let sc_k0: uint256 = uint256(((sc_x >> 8) & 3));\n        let sc_r: word = 0;\n        sc_st.push(sc_v0);\n        sc_st.push(sc_v1);\n        sc_st.push(7);\n        let sc_s0 = sc_st[1:];\n        sc_st.pop();\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_s0[sc_k0]));\n        sc_st.setLength(3);\n        sc_st[0] /= sc_v1;\n        let sc_a0: uint256[] = sc_mk(sc_v0, sc_v1);\n        let sc_g0: uint256[][] = [sc_a0, sc_a0];\n        sc_inc(lidx(sc_g0[sc_k0], 1), sc_v0);\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_a0[1]));\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-memory-array-corpus.py`. -/
private def memoryBResults : List String := [
    "1099511628210",
    "2199023256421",
    "3298534884636",
    "281474976822015",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "4398046512843",
    "8796093025687",
    "374144419304053411936909671855009658056471436331577",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032"]

private def abiASource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\ncontract SynthesizedArrayAbi {\n    function run(sc_p0: calldata<uint16[]>, sc_p1: uint16[], input: uint256) public returns (uint16[]) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: uint16 = Typedef.abs((sc_x & 0xffff));\n        let sc_k0: uint256 = uint256(((sc_x >> 1) & 3));\n        let sc_r: word = 0;\n        let sc_s0 = sc_p0[:];\n        let sc_a0: uint16[] = toArray(sc_s0);\n        sc_p1[sc_k0] = sc_v0;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_p0[sc_k0]));\n        for (let sc_i: uint256 = 0; sc_i < sc_p0.length; sc_i += 1) {\n            sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_p0[sc_i]));\n        }\n        return sc_p1;\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-memory-array-corpus.py`. -/
private def abiAResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000003",
    "0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x6cc54a63",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x6cc54a63",
    "0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000003",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000032",
    "0x6cc54a63",
    "0x6cc54a63"]

private def abiBSource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_put(sc_c: memref<int8>, sc_w: int8) {\n    CanStore.store(sc_c, sc_w);\n}\n\nfunction sc_tail(sc_v: int8[], sc_s: uint256) returns (arraySlice<int8[]>) {\n    return sc_v[sc_s:];\n}\n\ncontract SynthesizedArrayAbi {\n    function run(sc_p0: int8[], input: uint256) public returns (int8[]) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: int8 = Typedef.abs(sc_x);\n        let sc_v1: int8 = Typedef.abs((sc_x + 128));\n        let sc_r: word = 0;\n        let sc_s0 = sc_tail(sc_p0, 1);\n        sc_put(lidx(sc_p0, 2), sc_v1);\n        let sc_g0: int8[][] = [[sc_v0, 7], [sc_v0]];\n        sc_g0[1] = sc_p0;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_g0[1][2]));\n        return toArray(sc_s0);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-memory-array-corpus.py`. -/
private def abiBResults : List String := [
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80",
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81",
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82",
    "0x6cc54a63",
    "0x6cc54a63",
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f",
    "0x6cc54a63",
    "0x6cc54a63",
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83",
    "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000008ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff87",
    "0x6cc54a63",
    "0x6cc54a63"]

private def fixtures : List (String × Profile × Plan × String × List String) := [
  ("memoryA", MemoryArrays.profile, memoryA, memoryASource, memoryAResults),
  ("memoryB", MemoryArrays.profile, memoryB, memoryBSource, memoryBResults),
  ("abiA", ArrayAbi.profile, abiA, abiASource, abiAResults),
  ("abiB", ArrayAbi.profile, abiB, abiBSource, abiBResults)]

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
  for code in ["11", "32", "41"] do
    ensure (texts.contains ("0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ code))
      ("the fixtures reach no Panic(0x" ++ code ++ ")")
  ensure (texts.contains "0x6cc54a63") "the fixtures reach no rejected element"
  for (name, sites) in [("memoryB", ["stale", "inc"]), ("abiB", ["memory"])] do
    let plan := ((fixtures.find? (·.1 == name)).map (·.2.2.1)).getD default
    let runs := plan.boundaryRuns
    for site in sites do
      ensure (runs.any fun (_, events) => events.any fun event => event == .panic site 0x32 || event == .panic site 0x11 ||
          event == .dirty site) s!"{name} never stops at {site}"
  ensure (abiB.abiShapes.contains ("encodings", ["canonical", "normalized"])) "abiB returns no normalized element"

/-! Admission. -/

private def observe : Step := .act (.observe (.length (.array (.var 0))))
private def literal : Step := .literal [.input 0]
private def write (target : Target) (index : Index) (form : Form) : Step := .act (.write target index (.input 0) form)

private def memoryBase : Plan := {
  element := ⟨false, 1⟩, values := [⟨0, false⟩], indices := [⟨0, 3, false⟩], params := [], result := .word,
  steps := [literal, observe]}

private def memoryRefusals : List (String × Plan) :=
  let base := memoryBase
  [("a 24-bit type", {base with element := ⟨false, 3⟩}), ("no value", {base with values := []}),
    ("four values", {base with values := [⟨0, false⟩, ⟨1, false⟩, ⟨3, false⟩, ⟨1, false⟩]}),
    ("a first offset", {base with values := [⟨1, false⟩]}),
    ("an offset outside the table", {base with values := [⟨0, false⟩, ⟨2, false⟩]}),
    ("a raw value", {base with values := [⟨0, true⟩]}),
    ("four indices", {base with indices := List.replicate 4 ⟨0, 3, false⟩}),
    ("a mask outside the table", {base with indices := [⟨0, 2, false⟩]}),
    ("a shift outside the table", {base with indices := [⟨4, 3, false⟩]}),
    ("a flagged shifted index", {base with indices := [⟨1, 3, true⟩]}),
    ("a parameter", {base with params := [⟨true, .literal 1, 0, false⟩]}),
    ("an array result", {base with result := .array (.var 0)}),
    ("no step", {base with steps := []}), ("thirteen steps", {base with steps := literal :: List.replicate 12 observe}),
    ("no observation", {base with steps := [literal]}),
    ("a name before its declaration", {base with steps := [observe, literal]}),
    ("five arrays", {base with steps := List.replicate 5 literal ++ [observe]}),
    ("a literal of five values", {base with steps := [.literal (List.replicate 5 (.input 0)), observe]}),
    ("an index literal past 7", {base with steps := [literal, write (.array (.var 0)) (.literal 8) .plain, observe]}),
    ("the counter outside the loop", {base with steps := [literal, write (.array (.var 0)) .counter .plain, observe]}),
    ("a value past the literals", {base with steps := [.literal [.literal 8], observe]}),
    ("a length literal past 4", {base with steps := [.alloc (.literal 5), observe]}),
    ("a length past the indices", {base with steps := [.alloc (.input 1), observe]}),
    ("a flagged setLength", {base with indices := [⟨0, 3, true⟩], steps := [.setLength (.input 0), observe]}),
    ("nine pushes", {base with steps := List.replicate 9 (.push (.input 0)) ++ [observe]}),
    ("a memref write to the storage array", {base with steps := [.push (.input 0), write .storage (.literal 0) .put, observe]}),
    ("a loop over more than four elements", {base with
      indices := [⟨0, 7, false⟩]
      steps := [.alloc (.input 0), .loop (.array (.var 0)) [.observe (.length (.array (.var 0)))]]}),
    ("two loops", {base with steps := [literal, .loop (.array (.var 0)) [.observe (.length (.array (.var 0)))],
      .loop (.array (.var 0)) [.observe (.length (.array (.var 0)))]]}),
    ("a loop of three actions", {base with steps := [literal, .loop (.array (.var 0)) (List.replicate 3
      (.observe (.length (.array (.var 0)))))]}),
    ("four slices", {base with steps := literal :: List.replicate 4 (.slice (.array (.var 0)) .all) ++ [observe]}),
    ("three grids", {base with steps := literal :: List.replicate 3 (.grid (.literal 1)) ++ [observe]}),
    ("a grid of four arrays", {base with steps := [literal, .gridOf (List.replicate 4 (.var 0)), observe]}),
    ("a grid row of four values", {base with steps := [.gridLiteral [List.replicate 4 (.input 0)], literal, observe]}),
    ("a row replacement of no grid", {base with steps := [literal, .setRow 0 (.literal 0) (.var 0), observe]}),
    ("a copy of no slice", {base with steps := [.copy 0, observe]}),
    ("a calldata collection", {base with steps := [literal, .act (.observe (.length (.calldata 0)))]})]

private def abiBase : Plan := {
  element := ⟨true, 2⟩, values := [⟨0, false⟩], indices := [], params := [⟨false, .literal 2, 0, false⟩],
  result := .array (.param 0), steps := [.act (.observe (.length (.array (.param 0))))]}

private def abiRefusals : List (String × Plan) :=
  let base := abiBase
  [("no parameter", {base with params := []}), ("three parameters", {base with params := List.replicate 3 ⟨false, .literal 1, 0, false⟩}),
    ("a parameter length past 4", {base with params := [⟨false, .literal 5, 0, false⟩]}),
    ("a parameter shift outside the table", {base with params := [⟨false, .input 4 3, 0, false⟩]}),
    ("a parameter offset outside the table", {base with params := [⟨false, .literal 2, 2, false⟩]}),
    ("raw elements of a 256-bit type", {base with element := ⟨true, 32⟩, params := [⟨false, .literal 2, 0, true⟩]}),
    ("the storage array", {base with steps := [.push (.input 0)]}),
    ("a raw value with the fold", {base with values := [⟨0, true⟩], result := .word}),
    ("a raw value with a compound write", {base with
      values := [⟨0, true⟩]
      steps := [write (.array (.param 0)) (.literal 0) (.compound .add true)]}),
    ("a raw value with a sum", {base with values := [⟨0, true⟩], steps := [.act (.observe (.sum (.param 0)))]}),
    ("a write to a calldata parameter", {base with
      params := [⟨true, .literal 2, 0, false⟩]
      result := .word
      steps := [write (.array (.param 0)) (.literal 0) .plain, .act (.observe (.length (.calldata 0)))]}),
    ("a calldata parameter as an array result", {base with params := [⟨true, .literal 2, 0, false⟩]}),
    ("a copy of no slice", {base with result := .copy 0}),
    ("the fold without an observation", {base with result := .word, steps := [literal]})]

private def admissionChecks : IO Unit := do
  for (label, plan) in memoryRefusals do
    ensure (!plan.memoryAdmitted) ("memory array admission accepted " ++ label)
  for (label, plan) in abiRefusals do
    ensure (!plan.abiAdmitted) ("array ABI admission accepted " ++ label)
  for plan in [memoryBase, memoryA, memoryB] do
    ensure plan.memoryAdmitted ("memory array admission refused a control: " ++ reprStr plan)
    ensure (!plan.abiAdmitted) "array ABI admission accepted a memory array plan"
  for plan in [abiBase, abiA, abiB] do
    ensure plan.abiAdmitted ("array ABI admission refused a control: " ++ reprStr plan)
    ensure (!plan.memoryAdmitted) "memory array admission accepted an array ABI plan"

/-! The reference against the interpreter. -/

private def modelChecks : IO Unit := do
  let mut outcomes := 0
  let mut stops : List String := []
  let mut returns := 0
  for (generate, admitted) in [(generateMemory, Plan.memoryAdmitted), (generateAbi, Plan.abiAdmitted)] do
    let mut checked := 0
    for seed in List.range 200 do
      let plan := (generate (UInt64.ofNat seed)).fit Arrays.defaultNodes
      unless admitted plan do continue
      ensure (plan.applied Word.zero).check s!"seed {seed} failed the Core checker"
      checked := checked + 1
      for input in inputs do
        let expected := interpreterText plan input
        ensure (referenceText plan input == expected) s!"seed {seed}: reference and interpreter differ at {input}"
        outcomes := outcomes + 1
        if expected.startsWith "0x4e487b71" || expected == "0x6cc54a63" then
          unless stops.contains expected do stops := stops ++ [expected]
        else returns := returns + 1
    ensure (checked ≥ 190) s!"only {checked} of 200 seeds drew an admitted plan"
  ensure (outcomes ≥ 4560 && returns > 1000) s!"the model checks reached {outcomes} outcomes, {returns} returns"
  ensure (stops.length == 6) s!"the model checks reached {stops.length} kinds of revert data"

/-! Generation and replay. -/

private def shapeValues (shapes : List (String × List String)) : List (String × String) :=
  shapes.flatMap fun (dimension, values) => values.map (dimension, ·)

private def generationChecks : IO Unit := do
  for (profile, count, inventory) in [(MemoryArrays.profile, 2200, memoryShapeInventory),
      (ArrayAbi.profile, 500, abiShapeInventory)] do
    let mut seen : List (String × String) := []
    for seed in List.range count do
      let plan := (profile.generate (UInt64.ofNat seed)).fit Arrays.defaultNodes
      ensure (plan == (profile.generate (UInt64.ofNat seed)).fit Arrays.defaultNodes) "generation is not deterministic"
      for value in shapeValues (profile.shapes plan) do
        unless seen.contains value do seen := seen ++ [value]
    let all := shapeValues inventory
    for value in seen do
      ensure (all.contains value) s!"{profile.label}: {value.1} {value.2} is outside the inventory"
    for value in all do
      ensure (seen.contains value) s!"{profile.label}: {value.1} {value.2} is never drawn"
    let corpus := profile.generateCases (Seed.ofNat 1) Arrays.defaultNodes 64 400 fuel
    let cases ← expect (corpus.getObjValAs? (Array Json) "cases")
    ensure (cases.size == 64) (profile.label ++ ": generation did not complete 64 cases")
    for case in cases do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a generated case does not replay")
    let seeded := profile.generateCases (Seed.ofNat 7) Arrays.defaultNodes 24 400 fuel .seeded .nonIdentity
    for case in ← expect (seeded.getObjValAs? (Array Json) "cases") do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a seeded case does not replay")
    let small := (List.range 200).any fun seed =>
      ((profile.generate (UInt64.ofNat seed)).fit profile.minimumNodes).steps.length <
        (profile.generate (UInt64.ofNat seed)).steps.length
    ensure small (profile.label ++ ": the minimum budget never drops a step")
    let below := profile.generateCases (Seed.ofNat 1) (profile.minimumNodes - 1) 8 8 fuel
    ensure ((below.getObjValAs? (Array Json) "cases").toOption.map (·.size) == some 0)
      (profile.label ++ ": generation accepted a budget below the minimum")

/-! Tampering and reduction. -/

private def setObj (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | other => other

private def tamperChecks : IO Unit := do
  for (name, profile, plan, _, _) in fixtures do
    let some checkedPlan := Arrays.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError name)
    let case ← expect (profile.emitCase checkedPlan (Word.ofNatModulo 2) (Json.mkObj [("kind", toJson "imported")]) fuel)
    ensure ((profile.replayCase case fuel).toOption == some case) (name ++ " does not replay")
    let source ← expect (case.getObjValAs? String "source")
    let provenance ← expect (case.getObjVal? "provenance")
    let contract ← expect (case.getObjVal? "contract")
    let calldata ← expect (contract.getObjValAs? String "calldata")
    for (label, tampered) in [
        ("source", setObj case "source" (toJson (source ++ "\n"))),
        ("input", setObj case "input" (toJson "3")),
        ("program", setObj case "program" (Json.mkObj [])),
        ("plan", setObj case profile.planKey (profile.planJson {plan with steps := plan.steps.dropLast})),
        ("shapes", setObj case "provenance" (setObj provenance profile.shapesKey (Json.mkObj []))),
        ("generator version", setObj case "provenance" (setObj provenance "generatorVersion" (toJson "core-integers-v1"))),
        ("calldata", setObj case "contract" (setObj contract "calldata" (toJson (calldata ++ "00")))),
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
  let reduced (profile : Profile) (plan : Plan) : IO (List Plan) := do
    let some source := Arrays.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError "fixture")
    return (Arrays.reductions ⟨source, Word.ofNatModulo 2⟩).map (·.candidate.plan.plan)
  let looped : Plan := {memoryBase with
    steps := [literal, .loop (.array (.var 0)) [.observe (.element (.array (.var 0)) .counter)]]}
  ensure ((← reduced MemoryArrays.profile looped).contains {looped with
      steps := [literal, .act (.observe (.element (.array (.var 0)) (.literal 0)))]})
    "no reduction runs the loop's body once"
  let memory ← reduced MemoryArrays.profile memoryA
  ensure (memory.any fun plan => plan.steps.length < memoryA.steps.length) "no reduction removes a step"
  ensure (memory.any fun plan => plan.indices.length < memoryA.indices.length) "no reduction removes an index"
  let abi ← reduced ArrayAbi.profile abiB
  ensure (abi.contains {abiB with params := [⟨false, .literal 3, 0, false⟩]}) "no reduction cleans the raw elements"
  ensure (abi.contains {abiB with result := .word, values := abiB.values.map ({· with raw := false})})
    "no reduction lowers the result to the fold"
  let two ← reduced ArrayAbi.profile abiA
  ensure (two.any fun plan => plan.params.length == 1) "no reduction removes the second parameter"

def testSourceArrayCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceArrayCases
