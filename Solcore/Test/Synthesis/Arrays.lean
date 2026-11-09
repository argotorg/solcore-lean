import Solcore.Synthesis.Internal.Arrays
import Solcore.Synthesis.Internal.AbiReturns
import Solcore.Synthesis.Internal.AbiValues

/-!
# Array profile tests

Memory arrays, array ABI, dynamic and nested arrays, and array returns.
-/

section
-- leanmerge: from Solcore.Test.SourceArrayCases
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
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_sum(sc_v: int8[]) returns (int8) {\n    let sc_t: int8 = 0;\n    for (let sc_i: uint256 = 0; sc_i < sc_v.length; sc_i += 1) {\n        sc_t += sc_v[sc_i];\n    }\n    return sc_t;\n}\n\nfunction sc_get<c>(sc_c: c, sc_i: uint256) returns (int8) where (c, uint256): RValueIdxAccess<int8> {\n    return ridx(sc_c, sc_i);\n}\n\ncontract SynthesizedMemoryArrays {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: int8 = Typedef.abs(sc_signextend(0, sc_x));\n        let sc_v1: int8 = Typedef.abs(sc_signextend(0, (sc_x + 128)));\n        let sc_v2: int8 = Typedef.abs(sc_signextend(0, (sc_x + 127)));\n        let sc_k0: uint256 = uint256((sc_x & 3));\n        let sc_k1: uint256 = uint256((sc_x & 0x8000000000000000000000000000000000000000000000000000000000000007));\n        let sc_r: word = 0;\n        let sc_a0: int8[] = new int8[](sc_k0);\n        let sc_a1: int8[] = [sc_v0, sc_v1, (-128)];\n        let sc_a2: int8[] = sc_a1;\n        sc_a2[1] += sc_v0;\n        let sc_s0 = sc_a1[0:sc_k0];\n        sc_a1[0] = sc_v1;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_s0[uint256(0)]));\n        let sc_g0: int8[][] = new int8[][](sc_k1);\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_g0.length));\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_sum(sc_a2)));\n        for (let sc_i: uint256 = 0; sc_i < sc_a0.length; sc_i += 1) {\n            unchecked {\n                sc_a0[sc_i] *= sc_v0;\n            }\n            sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_get(sc_a1, sc_i)));\n        }\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_a1[1]));\n        return uint256(sc_r);\n    }\n}\n"

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
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\nfunction sc_inc(sc_c: memref<uint256>, sc_w: uint256) {\n    CanStore.store(sc_c, (CanStore.load(sc_c) + sc_w));\n}\n\nfunction sc_mk(sc_p: uint256, sc_q: uint256) returns (uint256[]) {\n    return [sc_p, sc_q];\n}\n\ncontract SynthesizedMemoryArrays {\n    sc_st: uint256[];\n\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: uint256 = Typedef.abs(sc_x);\n        let sc_v1: uint256 = Typedef.abs((sc_x + 1));\n        let sc_k0: uint256 = uint256(((sc_x >> 8) & 3));\n        let sc_r: word = 0;\n        sc_st.push(sc_v0);\n        sc_st.push(sc_v1);\n        sc_st.push(7);\n        let sc_s0 = sc_st[1:];\n        sc_st.pop();\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_s0[sc_k0]));\n        sc_st.setLength(3);\n        sc_st[0] /= sc_v1;\n        let sc_a0: uint256[] = sc_mk(sc_v0, sc_v1);\n        let sc_g0: uint256[][] = [sc_a0, sc_a0];\n        sc_inc(lidx(sc_g0[sc_k0], 1), sc_v0);\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_a0[1]));\n        return uint256(sc_r);\n    }\n}\n"

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
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\ncontract SynthesizedArrayAbi {\n    function run(sc_p0: calldata<uint16[]>, sc_p1: uint16[], input: uint256) public returns (uint16[]) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: uint16 = Typedef.abs((sc_x & 0xffff));\n        let sc_k0: uint256 = uint256(((sc_x >> 1) & 3));\n        let sc_r: word = 0;\n        let sc_s0 = sc_p0[:];\n        let sc_a0: uint16[] = toArray(sc_s0);\n        sc_p1[sc_k0] = sc_v0;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_p0[sc_k0]));\n        for (let sc_i: uint256 = 0; sc_i < sc_p0.length; sc_i += 1) {\n            sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_p0[sc_i]));\n        }\n        return sc_p1;\n    }\n}\n"

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
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_put(sc_c: memref<int8>, sc_w: int8) {\n    CanStore.store(sc_c, sc_w);\n}\n\nfunction sc_tail(sc_v: int8[], sc_s: uint256) returns (arraySlice<int8[]>) {\n    return sc_v[sc_s:];\n}\n\ncontract SynthesizedArrayAbi {\n    function run(sc_p0: int8[], input: uint256) public returns (int8[]) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_v0: int8 = Typedef.abs(sc_x);\n        let sc_v1: int8 = Typedef.abs((sc_x + 128));\n        let sc_r: word = 0;\n        let sc_s0 = sc_tail(sc_p0, 1);\n        sc_put(lidx(sc_p0, 2), sc_v1);\n        let sc_g0: int8[][] = [[sc_v0, 7], [sc_v0]];\n        sc_g0[1] = sc_p0;\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(sc_g0[1][2]));\n        return toArray(sc_s0);\n    }\n}\n"

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
end

section
-- leanmerge: from Solcore.Test.SourceArrayReturnCases
/-! Generated array-return cases. The Core contract must equal the source model,
a slot map and std's encoder run over the elements' memory, on every
transaction of the generated sequences; each case must replay to itself; the
shell node counts must be the ones the definitions fix; generation must draw
every element type and count, every bank length and inner length; every reduction must
be a strictly smaller sealed case that replays; and a transaction that does not
carry its plan's shape must be refused. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnCases

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (Element Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def slots (values : List Word) : Json :=
  toJson ((values.zipIdx).map fun (value, slot) => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString value.val))])

/-- The Core rows of a scenario equal the model's, transaction by transaction. -/
private def sameAsModel (scenario : Solcore.Synthesis.Source.ArrayReturn.CheckedScenario) (fuel : Nat) (name : String) :
    IO Unit := do
  let history := Solcore.Synthesis.Source.ArrayReturn.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name}: history incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := ArrayReturnExecution.model scenario.plan.step fuel scenario.plan.shape.element
      scenario.transactions | throw (IO.userError s!"{name}: the source model failed")
  ensure (rows.size == modelled.length) s!"{name}: a row is missing"
  for (row, model) in rows.toList.zip modelled do
    ensure ((row.getObjValAs? String "status").toOption == some (if model.reverted then "reverted" else "returned") &&
        (row.getObjValAs? String "output").toOption == some (encodeBytesText model.output) &&
        (row.getObjVal? "committedStorage").toOption == some (slots model.slots))
      s!"{name}: the Core row differs from the source model: {row.compress}"
    -- A return carries the encoding's Words, a revert one Word.
    ensure (model.output.size == if model.reverted then 32 else 32 * scenario.plan.shape.wordCount)
      s!"{name}: the output has the wrong size"

private def shape (element : Element) (lengths : List Nat) (count : Nat := lengths.length) : Shape :=
  ⟨element, count, if element.dynamic then lengths else []⟩

def testSourceArrayReturnCases : IO Unit := do
  let fuel := 1000000
  -- The shells the definitions fix: 89 nodes for an empty array, 175 for three
  -- `bytes` elements whose second data Words are masked.
  for (element, lengths, count, nodes) in [(Element.words, [], 0, 89), (.words, [], 3, 111), (.fourBytes, [], 3, 123),
      (.bytes, [64, 64, 64], 3, 169), (.bytes, [63, 63, 63], 3, 175), (.bytes, [0, 0, 0], 3, 125),
      (.nested, [2, 2, 2], 3, 169), (.nested, [0], 1, 101)] do
    ensure (ArrayReturn.shellNodes (shape element lengths count) == nodes)
      s!"the {element.name} shell of {lengths} has {ArrayReturn.shellNodes (shape element lengths count)} nodes"
  let mut minimum := 1000
  let mut maximum := 0
  for element in Solcore.Synthesis.Source.ArrayReturn.elementTypes do
    for count in List.range 4 do
      for length in (if element.dynamic then List.range (element.maxLength + 1) else [0]) do
        let nodes := ArrayReturn.shellNodes (shape element (List.replicate count length) count)
        minimum := min minimum nodes
        maximum := max maximum nodes
  ensure (minimum == 89 && maximum == 175) s!"the shells range over {minimum}..{maximum} nodes"
  ensure (Solcore.Synthesis.Source.ArrayReturn.maxProgramNodes == 512) "the case limit changed"
  -- Random generation: revision three with eight transactions at both budgets,
  -- and the fixed corpora's revision one with three.
  let mut elements : List String := []
  let mut counts : List String := []
  let mut bytesLengths : List Nat := []
  let mut innerLengths : List Nat := []
  let mut cases : Array Json := #[]
  for (revision, transactions, count, nodes) in [(GeneratorRevision.v3, 8, 40, 384), (GeneratorRevision.v1, 3, 24, 384),
      (GeneratorRevision.v3, 4, 12, 512)] do
    let corpus := Solcore.Synthesis.Source.ArrayReturn.generateCases (Seed.ofNat 1) nodes count 512 fuel revision transactions
    ensure ((corpus.getObjValAs? String "status").toOption == some "complete") s!"{revision.version}: generation exhausted"
    let generated ← get (corpus.getObjValAs? (Array Json) "cases")
    for (json, index) in generated.zipIdx do
      let name := s!"{revision.version} {nodes} case {index}"
      ensure ((Solcore.Synthesis.Source.ArrayReturn.replayCase json fuel).toOption == some json) s!"{name}: replay differs"
      let scenario ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
      ensure (scenario.transactions.length == transactions) s!"{name}: wrong sequence length"
      sameAsModel scenario fuel name
      let source ← get (json.getObjValAs? String "source")
      ensure ((source.splitOn "public returns (uint256) {").length == 2 &&
          (source.splitOn "abi_encode(sc_items)").length == 2 && (source.splitOn "return_((sc_encoded + 32)").length == 2)
        s!"{name}: the emitted method differs"
      let current := scenario.plan.shape
      elements := (elements ++ [current.element.name]).eraseDups
      counts := (counts ++ [s!"{current.count}"]).eraseDups
      cases := cases.push json
  ensure (sameMembers elements ["uint256", "bytes4", "bytes", "uint256[]"]) s!"generation drew the element types {elements}"
  ensure (sameMembers counts ["0", "1", "2", "3"]) s!"generation drew the counts {counts}"
  -- The shape draws alone, over the first 256 seeds: every element type with
  -- every count, every bank length, a uniform partial-Word length and every
  -- inner length.
  let mut pairs : List String := []
  for index in List.range 256 do
    let current := Solcore.Synthesis.Source.ArrayReturn.generatedShape (Seed.ofNat (1 + index))
    pairs := (pairs ++ [s!"{current.element.name}:{current.count}"]).eraseDups
    if current.element == .bytes then bytesLengths := (bytesLengths ++ current.lengths).eraseDups
    if current.element == .nested then innerLengths := (innerLengths ++ current.lengths).eraseDups
  ensure ([0, 1, 2, 3].all fun count => ["uint256", "bytes4", "bytes", "uint256[]"].all fun element =>
      pairs.contains s!"{element}:{count}") s!"the shape draws missed an element type's count: {pairs}"
  for length in Solcore.Synthesis.Source.ArrayReturn.lengthBank do
    ensure (bytesLengths.contains length) s!"generation never drew bytes length {length}"
  ensure (bytesLengths.all (· ≤ 64) && bytesLengths.any (fun length => length % 32 != 0 &&
      !Solcore.Synthesis.Source.ArrayReturn.lengthBank.contains length))
    "generation drew a bytes length above 64 or no uniform partial-Word length"
  ensure (sameMembers innerLengths [0, 1, 2]) s!"generation drew the inner lengths {innerLengths}"
  -- Reductions: a dropped element, `uint256` elements and a shorter length
  -- come whenever they apply, and every emitted candidate replays as a
  -- strictly smaller sealed case that equals the model.
  for json in cases.toList.take 8 do
    let source ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
    let current := source.plan.shape
    let reduced := Solcore.Synthesis.Source.ArrayReturn.reductions source
    ensure (!reduced.isEmpty) "a case has no reduction"
    let same := fun (candidate : Solcore.Synthesis.Source.ArrayReturn.Reduction source) =>
      candidate.candidate.transactions.length == source.transactions.length
    ensure (current.count == 0 || reduced.any fun candidate => same candidate &&
        candidate.candidate.plan.shape.count + 1 == current.count) "no dropped element"
    ensure (current.element == .words || reduced.any fun candidate => same candidate &&
        candidate.candidate.plan.shape == ⟨.words, current.count, []⟩) "no uint256 elements"
    ensure (Solcore.Synthesis.Source.ArrayReturn.totalLength current == 0 || reduced.any fun candidate =>
        same candidate && candidate.candidate.plan.shape.element == current.element &&
        Solcore.Synthesis.Source.ArrayReturn.totalLength candidate.candidate.plan.shape <
          Solcore.Synthesis.Source.ArrayReturn.totalLength current) "no shorter inner length"
    ensure (reduced.all fun candidate => candidate.candidate.transactions.all
        (Solcore.Synthesis.Source.ArrayReturn.admits candidate.candidate.plan.shape))
      "a reduction left a transaction off its plan's shape"
    let shrunk ← get (Solcore.Synthesis.Source.ArrayReturn.shrinkCases json 64 fuel)
    for candidate in ← get (shrunk.getObjValAs? (Array Json) "cases") do
      ensure ((Solcore.Synthesis.Source.ArrayReturn.replayCase candidate fuel).toOption == some candidate)
        "a reduction does not replay"
      sameAsModel (← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram candidate)) fuel "reduction"
  -- A transaction off its plan's shape is refused even with its own calldata:
  -- another length, another choice, or another digit of an inner length.
  let some json := cases.toList.find? (fun json => (json.getObjVal? "arrayReturnPlan").toOption.any
      fun plan => (plan.getObjValAs? String "elements").toOption == some "bytes" &&
        (plan.getObjValAs? Nat "count").toOption.any (· ≥ 2)) | throw (IO.userError "no bytes case")
  let scenario ← get (Solcore.Synthesis.Source.ArrayReturn.caseProgram json)
  let transactions ← get (json.getObjValAs? (Array Json) "transactions")
  let first := transactions[0]!
  let some tx := scenario.transactions.head? | throw (IO.userError "no transaction")
  for (choice, length) in [(tx.choice, tx.length + Word.ofNatModulo 4), (tx.choice + Word.ofNatModulo 1, tx.length),
      (tx.choice + Word.ofNatModulo 65, tx.length), (tx.choice, Word.ofNatModulo 0)] do
    let changed := first.setObjVal! "choice" (toJson (toString choice.val)) |>.setObjVal! "length"
      (toJson (toString length.val)) |>.setObjVal! "calldata"
      (toJson (ArrayReturnExecution.calldata tx.flags tx.input choice length))
    ensure (Solcore.Synthesis.Source.ArrayReturn.caseProgram
        (json.setObjVal! "transactions" (.arr (transactions.set! 0 changed)))).toOption.isNone
      s!"a transaction with choice {choice.val} and length {length.val} was admitted"
  ensure (Solcore.Synthesis.Source.ArrayReturn.caseProgram (json.setObjVal! "transactions" (.arr (transactions.set! 0
      (first.setObjVal! "length" (toJson "7")))))).toOption.isNone
    "a length that differs from its calldata was admitted"
  -- Plans outside the shapes are refused.
  let plan ← get (json.getObjVal? "arrayReturnPlan")
  ensure (Solcore.Synthesis.Source.ArrayReturn.checkedPlan (plan.setObjVal! "arity" (toJson 2))).toOption.isNone
    "a plan with an extra field was admitted"
  for (element, count, lengths) in [("bytes", 4, [0, 0, 0, 0]), ("bytes", 2, [0]), ("bytes", 1, [65]),
      ("uint256[]", 1, [3]), ("uint256", 1, [0]), ("bytes32", 1, []), ("SynthesizedEnum", 1, [])] do
    ensure (Solcore.Synthesis.Source.ArrayReturn.checkedPlan (plan.setObjVal! "elements" (toJson element)
        |>.setObjVal! "count" (toJson count) |>.setObjVal! "lengths" (toJson lengths))).toOption.isNone
      s!"the plan {element} {count} {lengths} was admitted"
where
  sameMembers {α : Type} [BEq α] (left right : List α) : Bool := left.all right.contains && right.all left.contains

end Tests.SourceArrayReturnCases
end

section
-- leanmerge: from Solcore.Test.SourceArrayReturnCorpus
/-! The fixed array-return corpus checks actual original Core histories against
expectations computed without the Core contract: the source model, a slot map
and std's encoder run over the elements' memory, in which each step runs alone
in Core. Coverage describes the checked steps' AST, the inputs, every element
type with every count, each element type's outcomes, the returned `bytes` and
inner lengths, the carries into a returned array from an earlier committed
transaction and past a revert, the node budgets of generated entries and the
completions. Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", ArrayReturn.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.ArrayReturn.version),
  ("templateVersion", ArrayReturn.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", ArrayReturn.emitterVersion), ("wrapperVersion", ArrayReturn.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

private def elementNames : List String := ArrayReturn.elementTypes.map (·.name)

/-- Every element type with every count from 0 to 3. -/
def shapeClasses : List String :=
  elementNames.flatMap fun element => (List.range 4).map fun count => s!"{element}:{count}"

/-- Every element type with both outcomes. -/
def outcomeClasses : List String :=
  elementNames.flatMap fun element => ["returned", "reverted"].map fun status => s!"{element}:{status}"

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := ArrayReturn.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← ArrayReturn.checkedPlan (← entry.getObjVal? "arrayReturnPlan")
  let scenario ← ArrayReturn.checkedScenario plan
    (← ArrayReturn.decodeTransactions plan.shape (← entry.getObjVal? "transactions"))
  ArrayReturn.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "array-return-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

/-- The source model's rows of a scenario, in the corpus's expected-row form. -/
def modelRows (scenario : ArrayReturn.CheckedScenario) (fuel : Nat) : Except String (List Json) := do
  let some rows := Solcore.Synthesis.Stateful.ArrayReturnExecution.model scenario.plan.step fuel
      scenario.plan.shape.element scenario.transactions | throw "the source model failed"
  return (rows.zip scenario.transactions).map fun (row, transaction) => Json.mkObj [
    ("id", toJson transaction.id), ("status", toJson (if row.reverted then "reverted" else "returned")),
    ("output", toJson (Solcore.ContractRuntime.encodeBytesText row.output)),
    ("committedStorage", toJson (row.slots.zipIdx.map fun (value, slot) => Json.mkObj [
      ("slot", toJson (toString slot)), ("value", toJson (toString value.val))]))]

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-array-returns" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected array-return manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("array-return manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words ArrayReturn.boundaryInputs))
    "array-return corpus must require all six boundary inputs"
  require ((← strings manifest "requiredArrayReturnShapes") == shapeClasses &&
    (← strings manifest "requiredArrayReturnOutcomes") == outcomeClasses)
    "array-return corpus must require every element type with every count and both outcomes"
  require ((← manifest.getObjValAs? (List Nat) "requiredArrayReturnBytesLengths") == ArrayReturn.lengthBank &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayReturnInnerLengths") == [0, 1, 2] &&
    (← manifest.getObjValAs? (List Nat) "requiredArrayReturnNodeBudgets") == [384, 512])
    "array-return corpus must require the bank's bytes lengths, every inner length and both node budgets"
  require ((← strings manifest "requiredArrayReturnCarries") == ["committed", "rollback"])
    "array-return corpus must require carries from a committed transaction and past a revert"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "array-return corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "array-return corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "array-return corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "array-return corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "array-return corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut shapes : List String := []
  let mut outcomesByElement : List String := []
  let mut bytesLengths : List Nat := []
  let mut innerLengths : List Nat := []
  let mut carries : List String := []
  let mut budgets : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate array-return corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← ArrayReturn.replayCase saved fuel) == saved) ("array-return corpus entry did not replay: " ++ identifier)
    let scenario ← ArrayReturn.caseProgram saved
    if let .ok request := entry.getObjVal? "generation" then
      budgets := (budgets ++ [← request.getObjValAs? Nat "maxProgramNodes"]).eraseDups
    else
      require ((← saved.getObjVal? "arrayReturnPlan") == (← entry.getObjVal? "arrayReturnPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported array-return entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("array-return corpus features changed: " ++ identifier)
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (expected == (← modelRows scenario fuel))
      ("the expected history differs from the source model: " ++ identifier)
    let history := ArrayReturn.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("array-return corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    require (observed.length == expected.length) ("array-return expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the source model: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ words (scenario.transactions.map (·.input))).eraseDups
    let shape := scenario.plan.shape
    for status in statuses do
      outcomesByElement := (outcomesByElement ++ [s!"{shape.element.name}:{status}"]).eraseDups
    if statuses.contains "returned" then
      shapes := (shapes ++ [s!"{shape.element.name}:{shape.count}"]).eraseDups
      if shape.element == .bytes then bytesLengths := (bytesLengths ++ shape.lengths).eraseDups
      if shape.element == .nested then innerLengths := (innerLengths ++ shape.lengths).eraseDups
    for (status, index) in statuses.zipIdx do
      if status == "returned" && (statuses.take index).contains "returned" then
        carries := (carries ++ ["committed"]).eraseDups
      if status == "returned" && (statuses.take index).contains "reverted" then
        carries := (carries ++ ["rollback"]).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "array-return corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "array-return corpus misses a boundary input"
  require (shapeClasses.all shapes.contains && outcomeClasses.all outcomesByElement.contains)
    "array-return corpus misses a returned element type and count, or an element type's outcome"
  require (ArrayReturn.lengthBank.all bytesLengths.contains && [0, 1, 2].all innerLengths.contains)
    "array-return corpus misses a returned bytes length or inner length"
  require (["committed", "rollback"].all carries.contains && [384, 512].all budgets.contains)
    "array-return corpus misses a carry or a node budget"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "array-return corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "array-return corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "array-return corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-array-returns"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("shapes", toJson shapes),
    ("bytesLengths", toJson bytesLengths), ("innerLengths", toJson innerLengths), ("carries", toJson carries),
    ("nodeBudgets", toJson budgets), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid array-return corpus unexpectedly passed")

def testSourceArrayReturnCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-array-return-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated array-return case")
  -- An imported `bytes` entry whose first transaction returns a partial last
  -- Word.
  let some first := entries.find? (fun entry => (entry.getObjVal? "arrayReturnPlan").toOption.any (fun plan =>
      (plan.getObjValAs? String "elements").toOption == some "bytes" &&
        (plan.getObjValAs? (List Nat) "lengths").toOption.any (·.any (· % 32 != 0))) &&
      (entry.getObjValAs? (Array Json) "expectedHistory").toOption.any (fun history =>
        history[0]?.any (fun row => (row.getObjValAs? String "status").toOption == some "returned"))) |
    throw (IO.userError "missing imported bytes case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  -- A changed head Word, a nonzero padding byte, a shorter output, a slot, a
  -- missing row and a status are all checked.
  let row := history[0]!
  let output ← checked (row.getObjValAs? String "output")
  let changedHead := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f') ++ output.drop 66))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedHead)))))
  let changedPadding := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 2)) ++
    (if output.endsWith "01" then "02" else "01")))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedPadding)))))
  let shorterOutput := row.setObjVal! "output" (toJson (String.ofList (output.toList.take (output.length - 64))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 shorterOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let slotTwo := (storage[2]!.getObjValAs? String "value").toOption
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 2
    (storage[2]!.setObjVal! "value" (toJson (if slotTwo == some "7" then "8" else "7")))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  -- A transaction's choice and length are checked against its calldata and
  -- the plan's shape, and the plan's shape against every transaction.
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  let length ← checked (transactions[0]!.getObjValAs? String "length")
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0
    (transactions[0]!.setObjVal! "length" (toJson (if length == "1" then "2" else "1"))))))))
  let flags ← checked (transactions[0]!.getObjValAs? String "flags")
  let input ← checked (transactions[0]!.getObjValAs? String "input")
  let choice ← checked (transactions[0]!.getObjValAs? String "choice")
  let some flagsValue := flags.toNat? | throw (IO.userError "invalid flags")
  let some inputValue := input.toNat? | throw (IO.userError "invalid input")
  let some choiceValue := choice.toNat? | throw (IO.userError "invalid choice")
  let some lengthValue := length.toNat? | throw (IO.userError "invalid length")
  let otherChoice := transactions[0]!.setObjVal! "choice" (toJson (toString (choiceValue + 1))) |>.setObjVal! "calldata"
    (toJson (Solcore.Synthesis.Stateful.ArrayReturnExecution.calldata (Word.ofNatModulo flagsValue)
      (Word.ofNatModulo inputValue) (Word.ofNatModulo (choiceValue + 1)) (Word.ofNatModulo lengthValue)))
  rejects (validateManifest (replace first (first.setObjVal! "transactions" (.arr (transactions.set! 0 otherChoice)))))
  let plan ← checked (first.getObjVal? "arrayReturnPlan")
  let count ← checked (plan.getObjValAs? Nat "count")
  let lengths ← checked (plan.getObjValAs? (List Nat) "lengths")
  rejects (validateManifest (replace first (first.setObjVal! "arrayReturnPlan" (plan.setObjVal! "count" (toJson (count - 1))
    |>.setObjVal! "lengths" (toJson lengths.dropLast)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredArrayReturnShapes", toJson (["uint256:0"] : List String)),
      ("requiredArrayReturnOutcomes", toJson (["uint256:returned"] : List String)),
      ("requiredArrayReturnBytesLengths", toJson [0, 1, 32]), ("requiredArrayReturnInnerLengths", toJson [0, 1]),
      ("requiredArrayReturnNodeBudgets", toJson [384]),
      ("requiredArrayReturnCarries", toJson (["committed"] : List String)),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceArrayReturnCorpus
end

section
-- leanmerge: from Solcore.Test.SourceArrayReturnGolden
/-! Golden cases for the array-return profile. Every expected row is written out
as hexadecimal Words computed outside Lean from the protocol and the ABI
encoding of `uint256[]`, `bytes4[]`, `bytes[]` and `uint256[][]`, not by
either model. The steps add a known constant `c`, so a transaction computes
`r = slot 0 + input + c`, writes `r` to slot 0, slot 1 plus one to slot 1 and the
input to slot 2, and returns std's encoding of the plan's array, element `i`
built from `a = r · K + i` and `b = ((slot 1 · K) xor (prior slot 2)) + i`: the
offset 32 and the length, then inline Words, or one offset per element and the
element tails. Odd flags revert with `r` and keep the prior slots. The scenarios
cover every element type, counts 0 to 3, the `bytes` lengths 0, 1, 31, 32, 33,
63 and 64, inner lengths 0 to 2, both outcomes, carries past a revert and
wrapping sums. Both the Core contract and the source model must give each row,
and a changed Word must be detected. -/
set_option autoImplicit false

namespace Tests.SourceArrayReturnGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (Element Shape)
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The step `x ↦ x + c`: aggregate template 0 around the constant scalar. -/
private def step (c : Nat) : IO Aggregates.CheckedDAG := do
  let some dag := Aggregates.CheckedDAG.ofParts? [Solcore.Synthesis.Source.Aggregate.template 0 (.word (w c))]
      (.apply (.var 1) (.var 0)) | throw (IO.userError "constant step failed admission")
  return dag

/-- The expected row: status, the whole output as hexadecimal Words and slots
zero to two. -/
private structure Expected where
  status : String
  output : List String
  values : List Nat

private def slots (values : List Nat) : Json :=
  toJson ((List.range ArrayReturn.slotCount).map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)), ("value", toJson (toString (values.getD slot 0)))])

private def tx (shape : Shape) (index flags input : Nat) : Transaction :=
  Solcore.Synthesis.Source.ArrayReturn.shaped shape ("tx-" ++ toString index) (w flags) (w input)

/-- `uint256`, three elements, `c = 1`: the Words `r · K + i`; a revert keeps the
slots; the last sum wraps: 14 + (2^256 - 1) + 1 = 14. -/
private def wordsShape : Shape := ⟨.words, 3, []⟩

private def wordsRows : List (Transaction × Expected) := [
  (tx wordsShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780"],
    [6, 1, 5]⟩),
  (tx wordsShape 1 1 9, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000010"],
    [6, 1, 5]⟩),
  (tx wordsShape 2 2 7, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc27",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc28"],
    [14, 2, 7]⟩),
  (tx wordsShape 3 0 (2 ^ 256 - 1), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc26",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc27",
      "a708a824f612c933529285451500f2d8e71e27e752e2407b95edccf96a95cc28"],
    [14, 3, (2 ^ 256 - 1)]⟩)]

/-- An empty array, `c = 0`: the offset and the length zero alone. -/
private def emptyShape : Shape := ⟨.words, 0, []⟩

private def emptyRows : List (Transaction × Expected) := [
  (tx emptyShape 0 0 3, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000000"],
    [3, 1, 3]⟩),
  (tx emptyShape 1 3 4, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000007"],
    [3, 1, 3]⟩)]

/-- `bytes4`, two elements, `c = 0`: the low four bytes of `r · K + i`,
left-aligned; a first revert from empty storage; the last sum wraps. -/
private def fourBytesShape : Shape := ⟨.fourBytes, 2, []⟩

private def fourBytesRows : List (Transaction × Expected) := [
  (tx fourBytesShape 0 1 1, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000001"],
    [0, 0, 0]⟩),
  (tx fourBytesShape 1 0 10, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "278f91d200000000000000000000000000000000000000000000000000000000",
      "278f91d300000000000000000000000000000000000000000000000000000000"],
    [10, 1, 10]⟩),
  (tx fourBytesShape 2 0 (2 ^ 256 - 2), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "860c74a800000000000000000000000000000000000000000000000000000000",
      "860c74a900000000000000000000000000000000000000000000000000000000"],
    [8, 2, (2 ^ 256 - 2)]⟩)]

/-- `bytes` of 31, 32 and 33 bytes, `c = 1`: the offsets 96, 160 and 224, a
data Word cut to 31 bytes, one whole Word, and a Word and one byte of
`((count · K) xor last) + 2`. -/
private def bytesWordsShape : Shape := ⟨.bytes, 3, [31, 32, 33]⟩

private def bytesWordsRows : List (Transaction × Expected) := [
  (tx bytesWordsShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "000000000000000000000000000000000000000000000000000000000000001f",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895700",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "0000000000000000000000000000000000000000000000000000000000000021",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780",
      "9e00000000000000000000000000000000000000000000000000000000000000"],
    [6, 1, 5]⟩),
  (tx bytesWordsShape 1 1 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000007"],
    [6, 1, 5]⟩),
  (tx bytesWordsShape 2 2 (2 ^ 255), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "000000000000000000000000000000000000000000000000000000000000001f",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae600",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae614",
      "0000000000000000000000000000000000000000000000000000000000000021",
      "d38454127b096499a94942a28a80796c738f13f3a971203dcaf6e67cb54ae615",
      "3c00000000000000000000000000000000000000000000000000000000000000"],
    [57896044618658097711785492504343953926634992332820282019728792003956564819975, 2, (2 ^ 255)]⟩)]

/-- `bytes` of 0, 63 and 64 bytes, `c = 0`: an empty element's length Word
alone, then both data Words, the second cut to 31 bytes, and both whole. -/
private def bytesEndsShape : Shape := ⟨.bytes, 3, [0, 63, 64]⟩

private def bytesEndsRows : List (Transaction × Expected) := [
  (tx bytesEndsShape 0 0 1, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000000000000000000000000000003f",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e96",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e00",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97"],
    [1, 1, 1]⟩),
  (tx bytesEndsShape 1 0 7, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000e0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000000000000000000000000000003f",
      "f1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c74a9",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d00",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "f1bbcdcbfa53e0af9ce60302e76e41a084113b5f9d13928fc363508e860c74aa",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d2d"],
    [8, 2, 7]⟩)]

/-- One `bytes` element of one byte, `c = 1`, around a revert; the last sum
wraps. -/
private def bytesOneShape : Shape := ⟨.bytes, 1, [1]⟩

private def bytesOneRows : List (Transaction × Expected) := [
  (tx bytesOneShape 0 0 3, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "7800000000000000000000000000000000000000000000000000000000000000"],
    [4, 1, 3]⟩),
  (tx bytesOneShape 1 3 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000005"],
    [4, 1, 3]⟩),
  (tx bytesOneShape 2 0 (2 ^ 256 - 1), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "7800000000000000000000000000000000000000000000000000000000000000"],
    [4, 2, (2 ^ 256 - 1)]⟩)]

/-- `uint256[]` of zero, one and two Words, `c = 1`: the inner lengths and
Words behind the offsets 96, 128 and 192. -/
private def nestedShape : Shape := ⟨.nested, 3, [0, 1, 2]⟩

private def nestedRows : List (Transaction × Expected) := [
  (tx nestedShape 0 0 5, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000c0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577f",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae4895780",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e97"],
    [6, 1, 5]⟩),
  (tx nestedShape 1 1 1, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000008"],
    [6, 1, 5]⟩),
  (tx nestedShape 2 0 2, ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000003",
      "0000000000000000000000000000000000000000000000000000000000000060",
      "0000000000000000000000000000000000000000000000000000000000000080",
      "00000000000000000000000000000000000000000000000000000000000000c0",
      "0000000000000000000000000000000000000000000000000000000000000000",
      "0000000000000000000000000000000000000000000000000000000000000001",
      "8ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033e",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "8ff34785799e5cc59082c363445c09d4949362cb90b604e1bbcfbaa056ce033f",
      "3c6ef372fe94f82be73980c0b9db906821044ed7e744e4a3f0d8d423a1831d31"],
    [9, 2, 2]⟩)]

/-- Two inner arrays of two and zero Words, `c = 0`, after a first revert. -/
private def nestedTwoShape : Shape := ⟨.nested, 2, [2, 0]⟩

private def nestedTwoRows : List (Transaction × Expected) := [
  (tx nestedTwoShape 0 1 0, ⟨"reverted", ["0000000000000000000000000000000000000000000000000000000000000000"],
    [0, 0, 0]⟩),
  (tx nestedTwoShape 1 0 (2 ^ 255), ⟨"returned", ["0000000000000000000000000000000000000000000000000000000000000020",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "0000000000000000000000000000000000000000000000000000000000000040",
      "00000000000000000000000000000000000000000000000000000000000000a0",
      "0000000000000000000000000000000000000000000000000000000000000002",
      "8000000000000000000000000000000000000000000000000000000000000000",
      "9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95",
      "0000000000000000000000000000000000000000000000000000000000000000"],
    [(2 ^ 255), 1, (2 ^ 255)]⟩)]

private def scenarios : List (String × Nat × Shape × List (Transaction × Expected)) := [
  ("words", 1, wordsShape, wordsRows),
  ("empty", 0, emptyShape, emptyRows),
  ("fourBytes", 0, fourBytesShape, fourBytesRows),
  ("bytesWords", 1, bytesWordsShape, bytesWordsRows),
  ("bytesEnds", 0, bytesEndsShape, bytesEndsRows),
  ("bytesOne", 1, bytesOneShape, bytesOneRows),
  ("nested", 1, nestedShape, nestedRows),
  ("nestedTwo", 0, nestedTwoShape, nestedTwoRows)]

/-- Whether original Core's row and the source model's row both equal the
expected row. -/
private def agrees (row : Json) (model : ArrayReturnExecution.ModelRow) (expected : Expected) : Bool :=
  let output := "0x" ++ String.join expected.output
  (row.getObjValAs? String "status").toOption == some expected.status &&
    (row.getObjValAs? String "output").toOption == some output &&
    (row.getObjVal? "committedStorage").toOption == some (slots expected.values) &&
    model.reverted == (expected.status == "reverted") && encodeBytesText model.output == output &&
    model.slots == (List.range ArrayReturn.slotCount).map (fun slot => w (expected.values.getD slot 0))

/-- Original Core's rows and the source model's rows of a scenario. -/
private def observed (constant : Nat) (shape : Shape) (transactions : List Transaction) :
    IO (List (Json × ArrayReturnExecution.ModelRow)) := do
  let fuel := 1000000
  let step ← step constant
  let some plan := ArrayReturn.CheckedPlan.ofParts? step shape
    | throw (IO.userError "the array-return wrapper failed admission")
  ensure (plan.contract.entryProfile == .wordTupleOutcomeV1 shape.bodyWords)
    "the contract does not use the Word-tuple convention of its encoding's Words"
  let history := ArrayReturnExecution.observe plan transactions StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") "the history is incomplete"
  let rows ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := ArrayReturnExecution.model step fuel shape.element transactions
    | throw (IO.userError "the source model failed")
  ensure (rows.size == transactions.length && modelled.length == transactions.length) "a row is missing"
  return rows.toList.zip modelled

def testSourceArrayReturnGolden : IO Unit := do
  ensure (Solcore.Synthesis.Source.ArrayReturn.multiplierLiteral ==
      "0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95")
    "the emitted multiplier differs from the defined constant"
  for (name, constant, shape, rows) in scenarios do
    let pairs ← observed constant shape (rows.map Prod.fst)
    for ((row, model), (transaction, expected)) in pairs.zip rows do
      ensure (agrees row model expected)
        s!"{name} {transaction.id}: original Core or the source model differs from the expected row {row.compress}"
  -- A changed Word, here the second element's Word of the first `uint256`
  -- row, is detected.
  let some (transaction, expected) := wordsRows.head? | throw (IO.userError "no uint256 row")
  let pairs ← observed 1 wordsShape [transaction]
  let some (row, model) := pairs.head? | throw (IO.userError "no observed row")
  let changed := expected.output.set 3 "b54cda58fbbee883b5ac82422d92b138630cec87b5ceadebd28a7c6ae489577e"
  ensure (!agrees row model {expected with output := changed}) "a changed Word was not detected"
  -- The 32nd byte of the 31-byte element's first data Word is nonzero in the
  -- method's memory and zero in the output.
  let some (transaction, expected) := bytesWordsRows.head? | throw (IO.userError "no bytes row")
  let a := w 6 * w ArrayReturn.multiplier
  ensure (a.val % 256 != 0) "the memory byte after the 31-byte element is zero"
  let some data := expected.output[6]? | throw (IO.userError "no data Word")
  ensure (data.endsWith "00" && data.take 62 == (String.ofList (Nat.toDigits 16 a.val)).take 62)
    "the 31-byte element is not its Word cut to 31 bytes"
  let pairs ← observed 1 bytesWordsShape [transaction]
  let some (row, model) := pairs.head? | throw (IO.userError "no observed row")
  ensure (agrees row model expected) "the 31-byte element's padding is not zero"

end Tests.SourceArrayReturnGolden
end

section
-- leanmerge: from Solcore.Test.SourceDynamicArrayCases
/-! Dynamic-array case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction and calldata boundaries, and
typed reductions over steps, transactions, array elements and flags. Expected
values here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceDynamicArrayCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicArrayExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "array fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "array wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × List Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, elements), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, elements.map Word.ofNatModulo⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List Nat)) : IO DynamicArray.CheckedScenario :=
  get (DynamicArray.checkedScenario plan (transactions values))
private def imported (value : DynamicArray.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (DynamicArray.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, [1, 3, 7]), (1, [2 ^ 256 - 1]), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1", "2", "3", "4"] : List String))
    "case did not declare slots zero through four"
  ensure ((← get (DynamicArray.replayCase saved 10000)) == saved) "imported array case did not replay"
  ensure ((← get (DynamicArray.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "array replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, []), (2, [9, 9])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "array elements or flags were substituted into source or Core code"
  let observed := DynamicArray.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "array scenario did not follow its flags parities"
  let rebound ← rows (DynamicArray.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent array profile changed with bindings"
  rejected (DynamicArray.checkedScenario identity (transactions [(0, [1, 2, 3, 4])])) "four-element array accepted"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := DynamicArray.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 16 && (choices.zip DynamicArray.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match DynamicArray.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "array recipe lost node/transaction/helper bounds"
        ensure ((value.transactions.map (·.values.length)) == choices.take 3) "generated lengths escaped their draws"
        ensure (value.transactions.all (fun tx => tx.values.all DynamicArray.boundaryInputs.contains))
          "generated element escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == DynamicArray.generatedParities (Seed.ofNat seed))
          "generated flags lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (DynamicArray.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (DynamicArray.generatedScenario (Seed.ofNat 0) DynamicArray.programOverhead) "undersized node budget accepted"
  let corpus := DynamicArray.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == DynamicArray.generateCases (Seed.ofNat 0) 384 4 512 10000) "array generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "array count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (DynamicArray.replayCase saved 10000)) == saved) "generated array provenance did not replay"
    let low ← get (DynamicArray.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := DynamicArray.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "array generation resource exhaustion was not distinguished"
  ensure ((← rows (DynamicArray.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (DynamicArray.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (DynamicArray.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "array generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("values", toJson (["01"] : List String)),
      ("values", toJson (["1", "3"] : List String)), ("values", toJson (["1", "2", "3", "4"] : List String)),
      ("values", toJson "1"), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (DynamicArray.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical array transaction accepted"
  rejected (DynamicArray.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (DynamicArray.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (DynamicArray.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0", "1", "2", "3"] : List String)),
      ("observedSlots", toJson (["1", "0", "2", "3", "4"] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("dynamicArrayPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (DynamicArray.caseProgram (saved.setObjVal! name bad)) "invalid array case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (DynamicArray.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered array provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (DynamicArray.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated array recipe accepted"
  let plan ← field saved "dynamicArrayPlan"
  rejected (DynamicArray.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical array plan accepted"
  rejected (DynamicArray.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.keyed-storage-plan.v1")))
    "keyed plan schema accepted as an array plan"
  rejected (DynamicArray.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (DynamicArray.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x7357f5d2"))) 10000)
    "two-Word selector accepted for the array ABI"
  rejected (DynamicArray.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-keyed-storage-case.v1")) 10000)
    "keyed case schema accepted by the array tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(2 ^ 256 - 2, [2 ^ 256 - 1, 7]), (2 ^ 255 + 1, [2 ^ 255]), (4, [3, 3, 3])]
  let saved ← imported value
  let candidates ← get (DynamicArray.shrinkCases saved 2000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (DynamicArray.shrinkCases saved 2000 10000)))
    "array reductions were empty or nondeterministic"
  let mut removed := false
  let mut removedElement := false
  let mut loweredElement := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (DynamicArray.caseProgram row)
    ensure (decide (DynamicArray.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "array reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", DynamicArray.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate array reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    removedElement := removedElement || (sameCount && DynamicArray.elementCount reduced < DynamicArray.elementCount value)
    loweredElement := loweredElement || (sameCount && pairs.any fun (left, right) =>
      left.values.length == right.values.length && (left.values.zip right.values).any fun (a, b) => a.val < b.val)
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (DynamicArray.replayCase row 10000)) == row) "reduced array case did not replay"
  ensure (removed && removedElement && loweredElement && loweredFlags && changedStep)
    "array shrink omitted sequence/element/value/flags/step axes"
  ensure ((← rows (← get (DynamicArray.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (DynamicArray.shrinkCases saved 0 10000)) "cases").isEmpty) "array shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (DynamicArray.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", DynamicArray.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", DynamicArray.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (DynamicArray.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict array reduction provenance accepted"

def testSourceDynamicArrayCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceDynamicArrayCases
end

section
-- leanmerge: from Solcore.Test.SourceDynamicArrayCorpus
/-! The fixed dynamic-array corpus checks actual original Core histories against
independently computed expectations: status, payload and slots zero to four
after every transaction. Coverage describes the checked step AST, the array
lengths and element values, and the completions. Source/Rust/EVM agreement is
a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceDynamicArrayCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", DynamicArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.DynamicArray.version),
  ("templateVersion", DynamicArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", DynamicArray.emitterVersion), ("wrapperVersion", DynamicArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := DynamicArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← DynamicArray.checkedPlan (← entry.getObjVal? "dynamicArrayPlan")
  let scenario ← DynamicArray.checkedScenario plan (← DynamicArray.decodeTransactions (← entry.getObjVal? "transactions"))
  DynamicArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "dynamic-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-dynamic-array" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected dynamic-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("dynamic-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words DynamicArray.boundaryInputs))
    "array corpus must require all six boundary elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredLengths") == [0, 1, 2, 3])
    "array corpus must require lengths zero through three"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut lengths : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← DynamicArray.replayCase saved fuel) == saved) ("array corpus entry did not replay: " ++ identifier)
    let scenario ← DynamicArray.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "dynamicArrayPlan") == (← entry.getObjVal? "dynamicArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("array corpus features changed: " ++ identifier)
    let history := DynamicArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("array corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("array expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => tx.values.map fun value => toString value.val).eraseDups
    lengths := (lengths ++ scenario.transactions.map (·.values.length)).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "array corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "array corpus misses a boundary element"
  require ([0, 1, 2, 3].all lengths.contains) "array corpus misses an array length"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-dynamic-array"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("lengths", toJson lengths), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid dynamic-array corpus unexpectedly passed")

def testSourceDynamicArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-dynamic-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated array case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned"))))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "values" (toJson (["4"] : List String))))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))]))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-keyed-storage"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredLengths", toJson [0, 1, 2]), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceDynamicArrayCorpus
end

section
-- leanmerge: from Solcore.Test.SourceDynamicArrayEmitter
/-! Dynamic-array protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: the fold over zero to three elements,
per-element slots that keep earlier values when a later array is shorter, the
running element count, zero writes as deletions and rollback of tentative
writes. The canonical calldata vectors were produced by Foundry `cast`. -/
set_option autoImplicit false

namespace Tests.SourceDynamicArrayEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError "array step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "array wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.DynamicArray.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"array source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × List Nat)) : List DynamicArrayExecution.Transaction :=
  rows.zipIdx.map fun ((flags, values), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, values.map Word.ofNatModulo⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Status, payload and slots zero to four after each transaction. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List Nat))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := DynamicArrayExecution.observeContract plan.contract (transactions rows)
    StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "array golden history did not complete"
  for (row, (status, payload, committed)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo payload))) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows committed))
      s!"array golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  let identity ← checked [.var 0]
  -- Three elements fold to 1, 4, 11; an odd-flags call folds 11 + max to 10
  -- before reverting; an empty array only rewrites the accumulator and count.
  historyCheck identity [(0, [1, 3, 7]), (1, [maximum]), (2, [])] [
    ("returned", 14, [11, 1, 4, 11, 3]),
    ("reverted", 14, [11, 1, 4, 11, 3]),
    ("returned", 14, [11, 1, 4, 11, 3])]
  -- A shorter array writes only its own element slots.
  historyCheck identity [(0, [5, 6, 7]), (2, [1])] [
    ("returned", 21, [18, 5, 11, 18, 3]),
    ("returned", 23, [19, 19, 11, 18, 4])]
  -- Zero results delete; reverted empty arrays keep the committed count.
  historyCheck (← checked [.var 0] (word 0)) [(0, [5, 6, 7]), (0, [1]), (7, [])] [
    ("returned", 3, [0, 0, 0, 0, 3]),
    ("returned", 4, [0, 0, 0, 0, 4]),
    ("reverted", 4, [0, 0, 0, 0, 4])]
  -- A fresh private cell per invocation; the arbitrary entry adds one overall.
  historyCheck (← checked [privateStep] (.binary .wordSub entry (word 1))) [(maximum - 1, [3]), (7, [1, 2, 3])] [
    ("returned", 5, [4, 4, 0, 0, 1]),
    ("reverted", 17, [4, 4, 0, 0, 1])]

/-- The reverted call's tentative world shows every element write and count. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "array contract did not resolve")
  let some input := DynamicArrayExecution.inputData? (Word.ofNatModulo 1)
      [Word.ofNatModulo 2, Word.ofNatModulo 3, Word.ofNatModulo 4] |
    throw (IO.userError "bounded array calldata was rejected")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed an array call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "array golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 12)))
        "odd flags did not revert with the tentative sum"
      let some working := result.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ([0, 1, 2, 3, 4].map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) == [9, 2, 5, 9, 3])
        "array writes were not applied in element order before the revert"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ([0, 1, 2, 3, 4].all (fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone) &&
        committed.balance == Word.zero && result.committedJournal.logList.isEmpty)
        "reverted array writes or unrelated effects were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [privateStep] (.binary .wordSub entry (word 1))] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "array plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (DynamicArray.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + DynamicArray.programOverhead)
      "array wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "array wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "array wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "array emission is nondeterministic"
  -- Raw primitives join the existing opcode import only when a step uses them.
  let divided ← checked [.binary .wordDiv (.var 0) (word 1)]
  match Solcore.Synthesis.Source.DynamicArray.emit divided with
  | .ok emitted => unless (emitted.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "DynamicArray emission lost the merged raw division alias or its snapshots")
  | .error error => throw (IO.userError s!"DynamicArray raw division was rejected: {reprStr error}")

private def elementLines (index : Nat) : List String :=
  ["        if (sc_length > " ++ toString index ++ ") {",
    "            let sc_value" ++ toString index ++ ": word = Typedef.rep(values[uint256(" ++ toString index ++ ")]);",
    "            sc_acc = sc_step(sc_acc + sc_value" ++ toString index ++ ");",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);", "        }"]

private def expectedBasic : String := String.intercalate "\n" ([
  "pragma solcore;", "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedDynamicArray {",
  "    function run(flags: uint256, values: calldata<array<uint256>>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_length: word = Typedef.rep(values.length());",
  "        let sc_acc: word = sload(0);"] ++ elementLines 0 ++ elementLines 1 ++ elementLines 2 ++ [
  "        sstore(0, sc_acc);",
  "        let sc_total: word = sload(4) + sc_length;", "        sstore(4, sc_total);",
  "        let sc_result: word = sload(0) + sload(4);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""])

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "dynamic-array protocol source changed"
  ensure (source.contractName == "SynthesizedDynamicArray" && source.methodSignature == "run(uint256,uint256[])" &&
    source.deployPath == ["SynthesizedDynamicArrayDeploy"] &&
    source.runtimePath == ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"])
    "array wrapper metadata changed"
  ensure (Solcore.Synthesis.Source.DynamicArray.emitterVersion == "solcore-source-dynamic-array-v3" &&
    Solcore.Synthesis.Source.DynamicArray.wrapperVersion == "solcore-word-dynamic-array-contract-v1" &&
    Solcore.Synthesis.Source.DynamicArray.selector == "0x9a94c44b" &&
    DynamicArray.version == "core-dynamic-array-contract-v1" && DynamicArray.maxElements == 3)
    "array provenance changed"

private def zeros (count : Nat) : String := String.ofList (List.replicate count '0')

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256[])" 1 "[5,6]"` and `0 "[]"`.
  ensure (DynamicArrayExecution.calldata (Word.ofNatModulo 1) [Word.ofNatModulo 5, Word.ofNatModulo 6] ==
    "0x9a94c44b" ++ zeros 63 ++ "1" ++ zeros 62 ++ "40" ++ zeros 63 ++ "2" ++ zeros 63 ++ "5" ++ zeros 63 ++ "6")
    "array calldata is not the canonical head/tail encoding"
  ensure (DynamicArrayExecution.calldata Word.zero [] == "0x9a94c44b" ++ zeros 64 ++ zeros 62 ++ "40" ++ zeros 64)
    "empty array calldata is not canonical"
  ensure (DynamicArrayExecution.observedSlots.map (·.val) == [0, 1, 2, 3, 4]) "array observed slots changed"
  let plan ← checked [.var 0]
  let calls := transactions [(2, [1]), (1, [2]), (0, [])]
  let exhausted := DynamicArrayExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 0
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "array observer conflated fuel exhaustion with completion"
  let complete := DynamicArrayExecution.observeContract plan.contract calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1", "2", "3", "4"] : List String)))
    "history did not declare its observed slots"

def testSourceDynamicArrayEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  formattingChecks
  observerChecks

end Tests.SourceDynamicArrayEmitter
end

section
-- leanmerge: from Solcore.Test.SourceNestedArrayCases
/-! Nested-array case regressions: exact replay, bounded generation from an
independent sequence stream, canonical values and nested calldata, and typed
reductions over steps, transactions, rows, elements and flags. Expected values
here are test goldens only; cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedArrayExecution (Transaction Bindings)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "nested-array fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "nested-array wrapper failed host admission")
  return plan
private def nested (rows : List (List Nat)) : List (List Word) := rows.map (·.map Word.ofNatModulo)
private def transactions (values : List (Nat × List (List Nat))) : List Transaction :=
  values.zipIdx.map fun ((flags, rows), index) => ⟨"call-" ++ toString index, Word.ofNatModulo flags, nested rows⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List (List Nat))) : IO NestedArray.CheckedScenario :=
  get (NestedArray.checkedScenario plan (transactions values))
private def imported (value : NestedArray.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (NestedArray.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, [[1, 3], [], [7]]), (1, [[maximum, high], [0]]), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((List.range 9).map toString))
    "case did not declare slots zero through eight"
  ensure ((← get (NestedArray.replayCase saved 1000000)) == saved) "imported nested-array case did not replay"
  ensure ((← get (NestedArray.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "nested-array replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, [[9]]), (2, [[], [], []])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "values or flags were substituted into source or Core code"
  ensure (((← rows saved).map fun row => (row.getObjVal? "values").toOption) ==
      #[some (toJson [["1", "3"], [], ["7"]]), some (toJson [[toString maximum, toString high], ["0"]]),
        some (toJson ([] : List (List String)))])
    "values are not canonical decimal rows"
  let observed := NestedArray.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "nested-array scenario did not follow its flags parities"
  ensure ((← get (NestedArray.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "nested-array history broke its row count, element count or sum protocol"
  let rebound ← rows (NestedArray.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent nested-array profile changed with bindings"
  rejected (NestedArray.checkedScenario identity (transactions [(0, [[], [], [], []])])) "four rows accepted"
  rejected (NestedArray.checkedScenario identity (transactions [(0, [[1, 2, 3]])])) "three elements in a row accepted"
  ensure (NestedArray.elementCount ⟨"x", Word.zero, nested [[1, 2], [], [3]]⟩ == 3 &&
    NestedArray.validValue (nested [[1, 2], [3, 4], [5, 6]]) && !NestedArray.validValue (nested [[], [], [], []]))
    "element count or value bound changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := NestedArray.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 31 && (choices.zip NestedArray.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match NestedArray.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + Solcore.Synthesis.Core.NestedArray.guardNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "nested-array recipe lost node/transaction/helper bounds"
        for (tx, index) in value.transactions.zipIdx do
          ensure (tx.values.length == choices.getD index 0) "generated outer length escaped its draw"
          for (cells, row) in tx.values.zipIdx do
            ensure (cells.length == choices.getD (3 + 3 * index + row) 0) "generated row length escaped its draw"
            for (cell, column) in cells.zipIdx do
              ensure (cell == NestedArray.boundaryInputs.getD (choices.getD (12 + 6 * index + 2 * row + column) 0) Word.zero)
                "generated element escaped its bank"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == NestedArray.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (NestedArray.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (NestedArray.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.NestedArray.programOverhead)
    "undersized node budget accepted"
  let corpus := NestedArray.generateCases (Seed.ofNat 0) 384 4 512 1000000
  ensure (corpus == NestedArray.generateCases (Seed.ofNat 0) 384 4 512 1000000) "nested-array generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "nested-array count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (NestedArray.replayCase saved 1000000)) == saved) "generated nested-array provenance did not replay"
    let low ← get (NestedArray.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := NestedArray.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "nested-array generation resource exhaustion was not distinguished"
  ensure ((← rows (NestedArray.generateCases (Seed.ofNat seed) 384 2 1 1000000) "cases").size == 1 &&
    (← natural (NestedArray.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (NestedArray.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "nested-array generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("values", toJson [["1", "3"], [], ["07"]]),
      ("values", toJson [["1", "3"], [], [toString (2 ^ 256)]]), ("values", toJson [["1", "3"], ["7"]]),
      ("values", toJson [["1", "3", "0"], [], ["7"]]), ("values", toJson [["1", "3"], [], ["7"], []]),
      ("values", toJson ["1", "3", "7"]), ("values", toJson [[1, 3], [], [7]]),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical nested-array transaction accepted"
  -- Calldata that names a different head offset or row offset is not canonical.
  let calldata ← string first "calldata"
  rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "0000000000000040" "0000000000000060"))]))
    "noncanonical head offset accepted"
  rejected (NestedArray.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "00000000000000c0" "00000000000000e0"))]))
    "noncanonical row offset accepted"
  rejected (NestedArray.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (NestedArray.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (NestedArray.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson ((List.range 10).map toString)),
      ("observedSlots", toJson (["0", "1", "2", "3", "4"] : List String)),
      ("observedSlots", toJson (["1", "0"] ++ (List.range 7).map (toString ∘ (· + 2)))),
      ("executionFuel", toJson (10000001 : Nat)), ("nestedArrayPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (NestedArray.caseProgram (saved.setObjVal! name bad)) "invalid nested-array case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (NestedArray.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered nested-array provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (NestedArray.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated nested-array recipe accepted"
  let generatedTransactions ← get (NestedArray.decodeTransactions (← field generated "transactions"))
  let some tx := generatedTransactions[0]? | throw (IO.userError "missing generated transaction")
  rejected (NestedArray.replayCase (generated.setObjVal! "transactions" (NestedArray.transactionsJson
      ({tx with values := tx.values ++ [[Word.ofNatModulo 1]]} :: generatedTransactions.drop 1))) 1000000)
    "generated value replaced without its seed"
  let plan ← field saved "nestedArrayPlan"
  rejected (NestedArray.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical nested-array plan accepted"
  rejected (NestedArray.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.dynamic-array-plan.v1")))
    "the flat array profile's plan schema accepted as a nested-array plan"
  rejected (NestedArray.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (NestedArray.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x9a94c44b"))) 1000000)
    "flat array selector accepted for the nested ABI"
  rejected (NestedArray.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-dynamic-array-case.v1")) 1000000)
    "the flat array profile's case schema accepted by the nested-array tool"

private def dropLastAt (values : List (List Word)) (row : Nat) : List (List Word) :=
  values.zipIdx.map fun (cells, current) => if current == row then cells.dropLast else cells

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(1, [[7, 3], [1]]), (0, [[maximum], [], [high, 1]]), (3, [[0, 7]])]
  let saved ← imported value
  let candidates ← get (NestedArray.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (NestedArray.shrinkCases saved 2000 1000000)))
    "nested-array reductions were empty or nondeterministic"
  let mut removed := false
  let mut removedRow := false
  let mut droppedElement := false
  let mut zeroed := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (NestedArray.caseProgram row)
    ensure (decide (NestedArray.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "nested-array reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", NestedArray.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate nested-array reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    removedRow := removedRow || (sameCount && pairs.any fun (left, right) =>
      (List.range right.values.length).any fun index => left.values == right.values.eraseIdx index)
    droppedElement := droppedElement || (sameCount && pairs.any fun (left, right) =>
      left.values != right.values &&
        (List.range right.values.length).any fun index => left.values == dropLastAt right.values index)
    zeroed := zeroed || (sameCount && pairs.any fun (left, right) =>
      left.values != right.values && left.values.map (·.length) == right.values.map (·.length) &&
        left.values.all (·.all (· == Word.zero)))
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (NestedArray.replayCase row 1000000)) == row) "reduced nested-array case did not replay"
  ensure (removed && removedRow && droppedElement && zeroed && loweredFlags && changedStep)
    "nested-array shrink omitted sequence/row/element/zero/flags/step axes"
  ensure ((← rows (← get (NestedArray.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (NestedArray.shrinkCases saved 0 1000000)) "cases").isEmpty) "nested-array shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (NestedArray.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", NestedArray.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", NestedArray.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (NestedArray.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict nested-array reduction provenance accepted"

def testSourceNestedArrayCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceNestedArrayCases
end

section
-- leanmerge: from Solcore.Test.SourceNestedArrayCorpus
/-! The fixed nested-array corpus checks actual original Core histories against
independently computed expectations: status, payload and slots zero to eight
after every transaction. Coverage describes the checked step AST, the elements
the step folds, the outer lengths, the row lengths and the completions.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def naturals (value : Json) (key : String) : Except String (List Nat) := do
  let values ← value.getObjValAs? (List Nat) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", NestedArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.NestedArray.version),
  ("templateVersion", NestedArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", NestedArray.emitterVersion), ("wrapperVersion", NestedArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := NestedArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← NestedArray.checkedPlan (← entry.getObjVal? "nestedArrayPlan")
  let scenario ← NestedArray.checkedScenario plan (← NestedArray.decodeTransactions (← entry.getObjVal? "transactions"))
  NestedArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "nested-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-nested-array" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected nested-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("nested-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Storage.boundaryInputs))
    "nested-array corpus must require all six boundary Words as elements"
  require (sameMembers (← naturals manifest "requiredRowCounts") (List.range 4))
    "nested-array corpus must require outer lengths zero to three"
  require (sameMembers (← naturals manifest "requiredRowLengths") (List.range 3))
    "nested-array corpus must require row lengths zero to two"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "nested-array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "nested-array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "nested-array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "nested-array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "nested-array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut rowCounts : List Nat := []
  let mut rowLengths : List Nat := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate nested-array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← NestedArray.replayCase saved fuel) == saved) ("nested-array corpus entry did not replay: " ++ identifier)
    let scenario ← NestedArray.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "nestedArrayPlan") == (← entry.getObjVal? "nestedArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported nested-array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("nested-array corpus features changed: " ++ identifier)
    let history := NestedArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← NestedArray.checkProtocol scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("nested-array expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      inputs := (inputs ++ words tx.values.flatten).eraseDups
      rowCounts := (rowCounts ++ [tx.values.length]).eraseDups
      rowLengths := (rowLengths ++ tx.values.map (·.length)).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "nested-array corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "nested-array corpus misses a boundary element"
  require ((List.range 4).all rowCounts.contains && (List.range 3).all rowLengths.contains)
    "nested-array corpus misses an outer length or a row length"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "nested-array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "nested-array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "nested-array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-nested-array"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("rowCounts", toJson rowCounts), ("rowLengths", toJson rowLengths),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid nested-array corpus unexpectedly passed: " ++ message))

def testSourceNestedArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-nested-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first nested-array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated nested-array case")
  -- A tampered entry goes first, so the validator rejects it before it
  -- replays the untouched entries; coverage does not depend on order.
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (#[changed] ++ entries.filter (· != original)))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (index : Nat) (row : Json) =>
    replace first (first.setObjVal! "expectedHistory" (.arr (history.set! index row)))
  let row := history[0]!
  rejects (validateManifest (withRow 0 (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 7 (storage[7]!.setObjVal! "value" (toJson "2")))))))
    "changed row count"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "4")))))))
    "changed element count"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 5 (storage[5]!.setObjVal! "value" (toJson "0")))))))
    "changed element result"
  rejects (validateManifest (withRow 0 (row.setObjVal! "committedStorage" (.arr (storage.set! 3 (storage[3]!.setObjVal! "value" (toJson "4")))))))
    "an absent element's slot written"
  -- The first scenario's second transaction reverts: committing its writes is wrong.
  let reverted := history[1]!
  let revertedStorage ← checked (reverted.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow 1 (reverted.setObjVal! "committedStorage"
    (.arr (revertedStorage.set! 7 (revertedStorage[7]!.setObjVal! "value" (toJson "5"))))))) "a reverted row count committed"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  -- Consistently re-encoded values with one changed element, one more empty
  -- row or one row fewer no longer match their history.
  let transactions ← checked (NestedArray.decodeTransactions (← checked (first.getObjVal? "transactions")))
  let some tx := transactions[0]? | throw (IO.userError "missing first nested-array transaction")
  let changed := {tx with values := tx.values.set 0 ((tx.values.getD 0 []).set 0 (Word.ofNatModulo 2))}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (changed :: transactions.drop 1))))) "changed element"
  let longer := {tx with values := tx.values.take 2 ++ [[]]}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (longer :: transactions.drop 1))))) "replaced row by an empty row"
  let shorter := {tx with values := tx.values.take 2}
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (NestedArray.transactionsJson (shorter :: transactions.drop 1))))) "dropped row"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (#[first] ++ entries)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-dynamic-array"), ("wrapperVersion", toJson "forged"),
      ("functionVersion", toJson "core-dynamic-array-contract-v2"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredRowCounts", toJson ([0, 1, 2] : List Nat)), ("requiredRowCounts", toJson ([0, 1, 2, 3, 4] : List Nat)),
      ("requiredRowLengths", toJson ([1, 2] : List Nat)), ("requiredRowLengths", toJson ([0, 1, 2, 3] : List Nat)),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceNestedArrayCorpus
end

section
-- leanmerge: from Solcore.Test.SourceNestedArrayEmitter
/-! Nested-array protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover ragged rows, an empty row,
an empty outer array, three empty rows, wrapping arithmetic, absent elements
whose slots stay untouched and a revert that keeps the prior slots. Calldata
vectors come from Foundry's `cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceNestedArrayEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def modulus : Nat := 2 ^ 256
private def maximum : Nat := modulus - 1
private def high : Nat := 2 ^ 255

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "nested-array step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "nested-array wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.NestedArray.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"nested-array source emission failed: {reprStr error}")

private def value (rows : List (List Nat)) : List (List Word) := rows.map (·.map Word.ofNatModulo)

private def transactions (rows : List (Nat × List (List Nat))) : List NestedArrayExecution.Transaction :=
  rows.zipIdx.map fun ((flags, values), index) => ⟨"tx-" ++ toString index, Word.ofNatModulo flags, value values⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexDigits (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def hexWord (value : Nat) : String := "0x" ++ hexDigits value

/-- One hand-computed row: status, payload and slots zero to eight. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List (List Nat)))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := NestedArrayExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 100000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows (List.replicate 9 0)))
    "nested-array golden history did not complete from empty storage"
  for (row, (status, payload, slots)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord (payload % modulus)) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows (slots.map (· % modulus))))
      s!"nested-array golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x + 1. Elements (0, 0), (0, 1) and (2, 0) write slots 1, 2 and
  -- 5; the empty row writes nothing. The second call keeps slots 2 and 5. The
  -- odd-flags revert writes 42 and 52 to slots 1 and 2 and returns
  -- 52 + 6 + 8, but keeps every slot.
  let afterSecond := [32, 15, 5, 23, 32, 9, 0, 5, 6]
  historyCheck (← checked [increment]) [(0, [[1, 2], [], [3]]), (0, [[5], [7, 8]]), (1, [[9, 9]])] [
    ("returned", 9 + 3 + 3, [9, 2, 5, 0, 0, 9, 0, 3, 3]),
    ("returned", 32 + 5 + 6, afterSecond),
    ("reverted", 52 + 6 + 8, afterSecond)]
  -- step(x) = x. The maximum plus one wraps the accumulator to zero; an empty
  -- outer array changes nothing; even flags 2 return; an empty first row and
  -- 2^255 + 2^255 wrap again, then 7 remains.
  let afterFirst := [0, maximum, 0, 0, 0, 0, 0, 1, 2]
  historyCheck (← checked [.var 0]) [(0, [[maximum, 1]]), (0, []), (2, [[], [high], [high, 7]])] [
    ("returned", 0 + 1 + 2, afterFirst),
    ("returned", 0 + 1 + 2, afterFirst),
    ("returned", 7 + 4 + 5, [7, maximum, 0, high, 0, 0, 7, 4, 5])]
  -- Three empty rows count as rows only.
  historyCheck (← checked [.var 0]) [(0, [[], [], []])] [("returned", 3, [0, 0, 0, 0, 0, 0, 0, 3, 0])]

/-- The reverted call's working world holds every write; the public runtime
commits the prior, here empty, world. -/
private def rollbackChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "nested-array contract did not resolve")
  let some input := NestedArrayExecution.inputData? (Word.ofNatModulo 1) (value [[1, 2], [], [3]]) |
    throw (IO.userError "nested-array calldata exceeded the Word-sized input bound")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  match TopLevelExecution.run contract invocation installed 100000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "nested-array golden call exhausted fuel")
  | .completed terminal =>
      ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo (6 + 3 + 3))))
        "odd flags did not revert with the tentative sum"
      let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ((List.range 9).map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) ==
          [6, 1, 3, 0, 0, 6, 0, 3, 3])
        "the working world lost an element, row count or element count write"
      let some committed := terminal.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ((List.range 9).all fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone)
        "the reverted writes were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "nested-array plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (NestedArray.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + NestedArray.programOverhead + NestedArray.guardNodes)
      "nested-array wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "nested-array wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "nested-array wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "nested-array emission is nondeterministic"
  ensure (NestedArray.programOverhead == 86 && NestedArray.guardNodes == 270 && NestedArray.maxRows == 3 &&
    NestedArray.maxColumns == 2 && NestedArray.rowSlot == 7 && NestedArray.cellSlot == 8)
    "nested-array wrapper size or layout changed"

/-- Element `(i, j)`'s four source lines, written out independently of the emitter. -/
private def expectedCell (row column : Nat) : List String :=
  ["            if (sc_width" ++ toString row ++ " > " ++ toString column ++ ") {",
    "                sc_acc = sc_step(sc_acc + Typedef.rep(sc_row" ++ toString row ++ "[uint256(" ++
      toString column ++ ")]));",
    "                sstore(" ++ toString (1 + 2 * row + column) ++ ", sc_acc);", "            }"]

private def expectedRow (row : Nat) : List String :=
  let i := toString row
  ["        if (sc_rows > " ++ i ++ ") {",
    "            let sc_row" ++ i ++ ": calldata<array<uint256>> = values[uint256(" ++ i ++ ")];",
    "            let sc_width" ++ i ++ ": word = Typedef.rep(sc_row" ++ i ++ ".length());",
    "            sc_cells = sc_cells + sc_width" ++ i ++ ";"] ++
    expectedCell row 0 ++ expectedCell row 1 ++ ["        }"]

private def expectedBasic : String := String.intercalate "\n" ([
  "pragma solcore;", "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedNestedArray {",
  "    function run(flags: uint256, values: calldata<array<calldata<array<uint256>>>>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_rows: word = Typedef.rep(values.length());",
  "        let sc_cells: word = 0;",
  "        let sc_acc: word = sload(0);"] ++
  expectedRow 0 ++ expectedRow 1 ++ expectedRow 2 ++ [
  "        sstore(0, sc_acc);",
  "        sstore(7, sload(7) + sc_rows);",
  "        sstore(8, sload(8) + sc_cells);",
  "        let sc_result: word = sload(0) + sload(7) + sload(8);",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""])

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "nested-array protocol source changed"
  ensure (source.contractName == "SynthesizedNestedArray" && source.methodSignature == "run(uint256,uint256[][])" &&
    source.deployPath == ["SynthesizedNestedArrayDeploy"] &&
    source.runtimePath == ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"])
    "nested-array wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, div as sc_div, ").length == 2)
    "nested-array emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.NestedArray.emitterVersion == "solcore-source-nested-array-v2" &&
    Solcore.Synthesis.Source.NestedArray.wrapperVersion == "solcore-word-nested-array-contract-v1" &&
    Solcore.Synthesis.Source.NestedArray.selector == "0x7095aff8" && NestedArray.version == "core-nested-array-contract-v1")
    "nested-array provenance changed"

/-- Calldata from the selector and the Words that `cast calldata` printed. -/
private def castCalldata (words : List Nat) : String := "0x7095aff8" ++ String.join (words.map hexDigits)

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256[][])" 1 VALUE` from the pinned Foundry release.
  for (rows, words) in [
      ([[5], [7, 8]], [1, 0x40, 2, 0x40, 0x80, 1, 5, 2, 7, 8]),
      ([], [1, 0x40, 0]),
      ([[], [4]], [1, 0x40, 2, 0x40, 0x60, 0, 1, 4]),
      ([[1, 2], [3, 4], [5, 6]], [1, 0x40, 3, 0x60, 0xc0, 0x120, 2, 1, 2, 2, 3, 4, 2, 5, 6])] do
    ensure (NestedArrayExecution.calldata (Word.ofNatModulo 1) (value rows) == castCalldata words)
      s!"nested calldata differs from the canonical head/tail encoding: {rows}"
  ensure ([[], [[]], [[1]], [[1, 2], [3, 4], [5, 6]]].map (fun rows =>
      (NestedArrayExecution.inputBytes Word.zero (value rows)).size) == [100, 164, 196, 484])
    "nested calldata sizes are not the head, the offset table, the row lengths and the elements"
  ensure (NestedArrayExecution.rowOffsets (value [[1, 2], [], [3]]) == [96, 192, 224])
    "row offsets are not measured from the start of the offset table"
  let plan ← checked [.var 0]
  let calls := transactions [(0, [[1]]), (1, [[2, 3]]), (0, [])]
  let exhausted := NestedArrayExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "nested-array observer conflated fuel exhaustion with completion"
  let complete := NestedArrayExecution.observe plan calls StorageExecution.fixtureBindings 100000
  ensure ((complete.getObjVal? "observedSlots").toOption ==
      some (toJson ((List.range 9).map toString)) &&
    (complete.getObjValAs? String "schema").toOption == some "solcore-lean.nested-array-history.v2" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its slots or schema"

def testSourceNestedArrayEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  rollbackChecks
  formattingChecks
  observerChecks

end Tests.SourceNestedArrayEmitter
end
