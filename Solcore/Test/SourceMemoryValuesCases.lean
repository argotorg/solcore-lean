import Solcore.Synthesis.Source.MemoryValuesCases
import Solcore.Abi.Keccak256

/-! The `runtime-memory-values` profile. Its Core reference models every
value as a byte list packed into Words; it agrees with a direct interpreter
of the plan over byte lists, with real loops, std's range checks and
`Solcore.Abi`'s Keccak-256, on generated plans, and a fixture's source and
results are golden, the results from a separate Python model. Admission
refuses steps, values, lengths, indices and loops outside the profile;
generation draws every shape and replays exactly; tampering is refused, and
reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceMemoryValuesCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.MemoryValues
open Solcore.Synthesis.Source

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private def fuel : Nat := 1000000

private def modulus : Nat := 2 ^ 256

private def cases (corpus : Json) : IO (Array Json) :=
  expect (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := expect (case.getObjVal? "provenance")

/-- A returned Word, or `none` for an out-of-range access. -/
private def run (program : Solcore.Core.Wire.Program) : IO (Option Nat) :=
  match program.toCore.runStateful fuel with
  | .done (.inLeft _ (.word value)) _ => pure (some value.val)
  | .done (.inRight _ .unit) _ => pure none
  | _ => throw (IO.userError "a reference program returned neither a Word nor an out-of-range access")

/-! A direct interpreter of a plan: bytes values as byte lists and arrays as
Word lists in a store of values, variables naming a value with a start and a
length, writes updating the store, loops run with their real counts and
std's range checks of `slice_`, `truncate` and `IndexAccess`. It shares no
code with the Core reference. -/

private structure Machine where
  input : Nat
  values : Array (Array Nat) := #[]
  vars : List ((String × Nat) × (Nat × Nat × Nat)) := []
  counts : List (String × Nat) := []
  acc : Nat := 0
  position : Nat := 0

/-- The only failure of an admitted plan is an out-of-range access. -/
private abbrev Interp := StateT Machine (Except String)

private def outOfRange {α : Type} : Interp α := throw "out of range"

private def operand (value : Operand) : Interp Nat := do
  let machine ← getThe Machine
  return match value with
    | .input => machine.input
    | .add constant => (machine.input + constant) % modulus
    | .mul constant => (machine.input * constant) % modulus
    | .xor constant => machine.input ^^^ constant
    | .acc => machine.acc
    | .counter => machine.position % modulus

private def index (value : Index) : Interp Nat := do
  let machine ← getThe Machine
  return match value with
    | .literal literal => literal
    | .input shift divisor => (machine.input >>> shift) % divisor
    | .counter scale offset => (machine.position * scale + offset) % modulus

private def key : Ref → String × Nat
  | .bytes number => ("bytes", number)
  | .slice number => ("slice", number)
  | .array number => ("array", number)

private def declare (kind : String) (entry : Nat × Nat × Nat) : Interp Unit := modify fun machine =>
  let number := (machine.counts.lookup kind).getD 0
  {machine with vars := ((kind, number), entry) :: machine.vars.filter (·.1 != (kind, number)),
                counts := (kind, number + 1) :: machine.counts.filter (·.1 != kind)}

private def entryOf (ref : Ref) : Interp (Nat × Nat × Nat) := do
  match (← getThe Machine).vars.lookup (key ref) with
  | some entry => return entry
  | none => throw "a variable out of scope"

private def bytesOf (ref : Ref) : Interp (List Nat) := do
  let (value, start, length) ← entryOf ref
  return (((← getThe Machine).values[value]!).toList.drop start).take length

private def wordBytes (value : Nat) : List Nat := (List.range 32).map fun index => (value / 256 ^ (31 - index)) % 256

private def bigEndian (bytes : List Nat) : Nat := bytes.foldl (fun total byte => total * 256 + byte) 0

private def keccak (bytes : List Nat) : Nat :=
  bigEndian ((Solcore.Abi.V1.Keccak256.hash (bytes.map UInt8.ofNat).toByteArray).toList.map (·.toNat))

private def part : Part → Interp (List Nat)
  | .word value => return wordBytes (← operand value)
  | .zeros count => return List.replicate count 0
  | .value ref => bytesOf ref

/-- `slice_(v, i)` then `truncate(·, width)`. -/
private def check (length position width : Nat) : Interp Unit :=
  if position > length || length - position < width then outOfRange else pure ()

private def store (value : Nat) (update : Array Nat → Array Nat) : Interp Unit := modify fun machine =>
  {machine with values := machine.values.modify value update}

private def access (ref : Ref) : Access → Interp Nat
  | .length => return (← entryOf ref).2.2
  | .hash => return keccak (← bytesOf ref)
  | .word position => do
      let (value, start, length) ← entryOf ref
      let offset ← index position
      check length offset 32
      return bigEndian ((((← getThe Machine).values[value]!).toList.drop (start + offset)).take 32)
  | .byte position => do
      let (value, start, length) ← entryOf ref
      let offset ← index position
      check length offset 1
      return ((← getThe Machine).values[value]!)[start + offset]!
  | .element position _ => do
      let (value, _, length) ← entryOf ref
      let offset ← index position
      if offset ≥ length then outOfRange
      return ((← getThe Machine).values[value]!)[offset]!

private def act : Action → Interp Unit
  | .bytes build => do
      let parts := match build with
        | .toBytes single => [single]
        | .concat left right => [left, right]
      let mut data : List Nat := []
      for single in parts do
        data := data ++ (← part single)
      let value := (← getThe Machine).values.size
      modify fun machine => {machine with values := machine.values.push data.toArray}
      declare "bytes" (value, 0, data.length)
  | .slice source cut => do
      let (value, start, length) ← entryOf source
      declare "slice" (match cut with
        | .drop dropped => (value, start + dropped, length - dropped)
        | .take kept => (value, start, kept)
        | .window dropped kept => (value, start + dropped, kept))
  | .alias source => do declare (key source).1 (← entryOf source)
  | .array _ elements => do
      let words ← elements.mapM operand
      let value := (← getThe Machine).values.size
      modify fun machine => {machine with values := machine.values.push words.toArray}
      declare "array" (value, 0, words.length)
  | .write target position written width _ => do
      let (value, start, length) ← entryOf target
      let offset ← index position
      let word ← operand written
      if target.isArray then
        if offset ≥ length then outOfRange
        store value (·.set! offset word)
      else match width with
        | .word =>
            check length offset 32
            store value fun bytes => (wordBytes word).zipIdx.foldl (fun bytes (byte, k) => bytes.set! (start + offset + k) byte) bytes
        | .byte =>
            check length offset 1
            store value (·.set! (start + offset) (word % 256))
  | .observe fold constant value observed => do
      let result ← access value observed
      modify fun machine =>
        let scaled := (machine.acc * constant) % modulus
        {machine with acc := match fold with
          | .add => (scaled + result) % modulus
          | .xor => scaled ^^^ result}

/-- Each iteration declares the body's variables again under the same
numbers; after the loop the numbering continues past them. -/
private def body (actions : List Action) : Interp Unit := do
  let counts := (← getThe Machine).counts
  for single in actions do act single
  modify fun machine => {machine with counts}

private def declared (actions : List Action) (kind : String) : Nat :=
  (actions.filter fun single => match single with
    | .bytes _ => kind == "bytes"
    | .slice .. => kind == "slice"
    | .array .. => kind == "array"
    | .alias source => (key source).1 == kind
    | _ => false).length

private def step : Step → Interp Unit
  | .action single => act single
  | .loop shape actions => do
      let machine ← getThe Machine
      let before := machine.counts
      match shape with
      | .single mask =>
          for counter in List.range (machine.input &&& mask) do
            modify fun machine => {machine with position := counter}
            body actions
      | .nested outer bound inner =>
          for i in List.range (machine.input &&& outer) do
            let count := match bound with
              | .input => machine.input &&& inner
              | .counter => (i + 1) &&& inner
            for j in List.range count do
              modify fun machine => {machine with position := i + j}
              body actions
      modify fun machine => {machine with counts := ["bytes", "slice", "array"].map fun kind =>
        (kind, (before.lookup kind).getD 0 + declared actions kind)}

/-- The returned Word, or `none` for an out-of-range access. -/
private def interpret (plan : Plan) (input : Nat) : Option (Option Nat) :=
  match ((plan.steps.forM step).run {input}) with
  | .ok ((), machine) => some (some machine.acc)
  | .error "out of range" => some none
  | .error _ => none

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 200 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  let mut outOfRanges := 0
  for seed in List.range 200 do
    match MemoryValues.generatedPlan (Seed.ofNat (seed + 1)) MemoryValues.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
          if core.isNone then outOfRanges := outOfRanges + 1
  ensure (compared = 2400) "fewer than 200 generated plans compared with the interpreter"
  ensure (outOfRanges ≥ 200) "fewer than 200 compared outcomes were out of range"

/-! A fixture with a copy, a window, a second variable, a helper's Word write
through it, a byte write through the slice at an input index, a hash of the
copy, and a nested loop reading and writing an array at its position beside
a copy of the slice in every iteration, then a Word read at an input index. -/

private def fixturePlan : Plan := {steps := [
  .action (.bytes (.concat (.word .input) (.word (.mul 3)))),
  .action (.bytes (.concat (.value (.bytes 0)) (.zeros 5))),
  .action (.slice (.bytes 0) (.window 7 40)),
  .action (.alias (.bytes 0)),
  .action (.array false [.add 7, .xor 255, .acc]),
  .action (.write (.bytes 2) (.literal 3) (.mul 5) .word .helper),
  .action (.write (.slice 0) (.input 1 45) .input .byte .inline),
  .action (.observe .add 5 (.bytes 1) .hash),
  .loop (.nested 3 .counter 3) [
    .observe .xor 7 (.array 0) (.element (.counter 1 0) true),
    .write (.array 0) (.counter 1 0) .acc .word .helper,
    .bytes (.toBytes (.value (.slice 0)))],
  .action (.observe .add 9 (.bytes 0) (.word (.input 3 40)))]}

/-- From the Python model of `Tests/scripts/test-semantic-memory-value-corpus.py`;
`none` is an out-of-range access. -/
private def fixtureResults : List (Nat × Option Nat) := [
  (0, some 21608449789222171400017857054612460352274887628236327849281298773463202112237),
  (1, some 37159832601512557076352362437260036118380150560180980217316581885928113078806),
  (2, some 7070914082375865400419380607351947518286818568728180506878057915024197659755),
  (255, none),
  (256, some 81253762954073271886094364441350933743392128171845494974348576044161271819597),
  (2 ^ 256 - 1, none),
  (2 ^ 255, some 115241369297029195970935126769825421674642356010695457834697403420591494212405),
  (2 ^ 255 - 1, none),
  (3, none),
  (5, some 58359939051907315747778763232000840318553681460026901230101664618625926483649),
  (77, some 59898808143498259735179537305375289661228902309705880128859437858850088642590),
  (1001, some 13800937350835242282643099520518083362978033394498188391394767143433918975331)]

private def fixtureSource : String := String.intercalate "\n" [
  "import * from std;",
  "import * from std.dispatch;",
  "import { mload, mstore, mstore8, shr, mod } from std.opcodes;",
  "",
  "function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
  "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));",
  "}",
  "",
  "function sc_put<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
  "    mstore(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)), sc_w);",
  "}",
  "",
  "function sc_aput(sc_a: memory<DynArray<uint256>>, sc_i: word, sc_w: word) returns (()) {",
  "    IndexAccess.set(sc_a, uint256(sc_i), uint256(sc_w));",
  "}",
  "",
  "contract SynthesizedMemoryValues {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = concat(bytes32(sc_x), bytes32((sc_x * 3)));",
  "        let sc_b1: memory<bytes> = concat(sc_b0, empty(5));",
  "        let sc_s0: memory_ref = truncate(slice_(sc_b0, 7), 40);",
  "        let sc_b2: memory<bytes> = sc_b0;",
  "        let sc_a0: memory<DynArray<uint256>> = [uint256((sc_x + 7)), uint256((sc_x ^ 255)), uint256(sc_r)];",
  "        sc_put(sc_b2, 3, (sc_x * 5));",
  "        mstore8(MemoryPointer.ptr(truncate(slice_(sc_s0, mod(shr(1, sc_x), 45)), 1)), sc_x);",
  "        sc_r = ((sc_r * 5) + Typedef.rep(keccak256_(sc_b1)));",
  "        let sc_outer: word = (sc_x & 3);",
  "        let sc_i: word = 0;",
  "        let sc_inner: word = 0;",
  "        let sc_j: word = 0;",
  "        while (sc_outer > sc_i) {",
  "            sc_inner = ((sc_i + 1) & 3);",
  "            sc_j = 0;",
  "            while (sc_inner > sc_j) {",
  "                sc_r = ((sc_r * 7) ^ Typedef.rep(IndexAccess.get(sc_a0, uint256((sc_i + sc_j)))));",
  "                sc_aput(sc_a0, (sc_i + sc_j), sc_r);",
  "                let sc_b3: memory<bytes> = to_bytes(sc_s0);",
  "                sc_j = (sc_j + 1);",
  "            }",
  "            sc_i = (sc_i + 1);",
  "        }",
  "        sc_r = ((sc_r * 9) + sc_word(sc_b0, mod(shr(3, sc_x), 40)));",
  "        return uint256(sc_r);",
  "    }",
  "}"] ++ "\n"

private def fixtureShapes : List (String × List String) := [
  ("values", ["alias:bytes", "array:literal", "bytes", "slice"]),
  ("parts", ["concat:bytes", "concat:word", "concat:zeros", "to_bytes:slice"]),
  ("cuts", ["window:bytes"]),
  ("writes", ["array:helper", "bytes:word:helper", "slice:byte:inline"]),
  ("observations", ["element:get", "hash:bytes", "word:bytes"]),
  ("indices", ["element:counter", "put8:input", "put:literal", "set:counter", "word:input"]),
  ("hazards", ["alias", "copy", "helper", "view"]),
  ("loops", ["nested:counter"]),
  ("body", ["bytes", "observe", "write"]),
  ("hashes", ["65-95"])]

private def fixtureChecks : IO Unit := do
  ensure fixturePlan.admitted "the fixture plan is not admitted"
  let some checked := MemoryValues.CheckedPlan.ofPlan? fixturePlan
    | throw (IO.userError "the fixture failed the checker")
  ensure ((MemoryValues.emit fixturePlan).source == fixtureSource) "the fixture source changed"
  for (value, expected) in fixtureResults do
    ensure ((← run (checked.program (Word.ofNatModulo value))) == expected) s!"fixture input {value}: Core result"
    ensure (interpret fixturePlan value == some expected) s!"fixture input {value}: interpreter result"
  ensure (fixturePlan.shapes == fixtureShapes) "the fixture shapes changed"
  ensure (match MemoryValues.planOf (MemoryValues.planJson fixturePlan) with
    | .ok plan => plan == fixturePlan
    | .error _ => false) "the fixture plan JSON does not round-trip"
  let observed := MemoryValues.observe checked (Word.ofNatModulo 255) fuel
  ensure (observed == Json.mkObj [("stage", toJson "execution"), ("status", toJson "reverted"),
    ("output", toJson "0xb4120f14")]) "an out-of-range fixture input is not observed as std's OutOfBounds() revert"

private def withStep (index : Nat) (replacement : Step) : Plan :=
  {steps := fixturePlan.steps.set index replacement}

private def fixtureLoop : List Action := match fixturePlan.steps[8]? with
  | some (Step.loop _ actions) => actions
  | _ => []

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let observe := Step.action (.observe .add 3 (.bytes 0) .length)
  let plan := fun (steps : List Step) => ({steps} : Plan)
  refused "no step" (plan ([]))
  refused "eleven steps" (plan (fixturePlan.steps ++ [observe]))
  refused "two loops" (plan (fixturePlan.steps.take 9 ++ [.loop (.single 1) [.observe .add 3 (.bytes 0) .length]]))
  refused "an empty loop" (withStep 8 (.loop (.single 3) []))
  refused "four loop actions" (withStep 8 (.loop (.single 3) (fixtureLoop ++ [.observe .add 3 (.bytes 0) .length])))
  refused "an alias in a loop" (withStep 8 (.loop (.single 3) [.alias (.bytes 0), .observe .add 3 (.bytes 3) .length]))
  refused "a loop-local variable after the loop" (withStep 9 (.action (.observe .add 9 (.bytes 3) .length)))
  refused "an undeclared variable" (withStep 7 (.action (.observe .add 5 (.bytes 3) .hash)))
  refused "a slice of an array" (withStep 2 (.action (.slice (.array 0) (.drop 1))))
  refused "a cut past the length" (withStep 2 (.action (.slice (.bytes 0) (.window 30 40))))
  refused "a value over 128 bytes" (plan ([.action (.bytes (.concat (.word .input) (.word .input))),
    .action (.bytes (.concat (.value (.bytes 0)) (.value (.bytes 0)))), .action (.bytes (.concat (.value (.bytes 1)) (.zeros 1))),
    observe]))
  refused "41 zero bytes" (withStep 1 (.action (.bytes (.concat (.value (.bytes 0)) (.zeros 41)))))
  refused "five bytes variables" (plan ((List.replicate 5 (.action (.bytes (.toBytes (.word .input))))) ++ [observe]))
  refused "four slices" (plan ([.action (.bytes (.toBytes (.word .input)))] ++
    List.replicate 4 (.action (.slice (.bytes 0) (.drop 1))) ++ [observe]))
  refused "three arrays" (plan (List.replicate 3 (.action (.array false [.input])) ++
    [.action (.observe .add 3 (.array 0) (.element (.literal 0) false))]))
  refused "an empty array" (withStep 4 (.action (.array false [])))
  refused "five elements" (withStep 4 (.action (.array true [.input, .input, .input, .input, .input])))
  refused "a Word access to 31 bytes" (plan ([.action (.bytes (.toBytes (.zeros 31))),
    .action (.observe .add 3 (.bytes 0) (.word (.input 0 9)))]))
  refused "a byte access to no bytes" (plan ([.action (.bytes (.toBytes (.zeros 0))),
    .action (.observe .add 3 (.bytes 0) (.byte (.input 0 9)))]))
  refused "a literal index past the end" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.word (.literal 33)))))
  refused "a modulus of zero" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.word (.input 3 0)))))
  refused "a modulus nine past the positions" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.word (.input 3 42)))))
  refused "an unlisted shift" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.word (.input 2 40)))))
  refused "a position index outside a loop" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.word (.counter 1 0)))))
  refused "a position Word outside a loop" (withStep 5 (.action (.write (.bytes 2) (.literal 3) .counter .word .helper)))
  refused "an unlisted scale" (withStep 8 (.loop (.nested 3 .counter 3)
    ((fixtureLoop.set 0 (.observe .xor 7 (.array 0) (.element (.counter 4 0) true))))))
  refused "an offset of nine" (withStep 8 (.loop (.nested 3 .counter 3)
    ((fixtureLoop.set 0 (.observe .xor 7 (.array 0) (.element (.counter 1 9) true))))))
  refused "an added zero" (withStep 4 (.action (.array false [.add 0, .xor 255, .acc])))
  refused "a product by one" (withStep 0 (.action (.bytes (.concat (.word .input) (.word (.mul 1))))))
  refused "an even fold constant" (withStep 7 (.action (.observe .add 4 (.bytes 1) .hash)))
  refused "a fold constant of 33" (withStep 7 (.action (.observe .add 33 (.bytes 1) .hash)))
  refused "a single mask of 2" (withStep 8 (.loop (.single 2) fixtureLoop))
  refused "a nested mask of 7" (withStep 8 (.loop (.nested 7 .counter 3) fixtureLoop))
  refused "no observation" (plan ([.action (.bytes (.toBytes (.word .input)))]))
  refused "eight hashes" (plan ([.action (.bytes (.toBytes (.word .input))),
    .loop (.single 7) [.observe .add 3 (.bytes 0) .hash], .action (.observe .add 3 (.bytes 0) .hash)]))
  refused "an element of bytes" (withStep 9 (.action (.observe .add 9 (.bytes 0) (.element (.literal 0) false))))
  refused "the length of an array" (withStep 9 (.action (.observe .add 9 (.array 0) .length)))
  refused "a byte write to an array" (withStep 5 (.action (.write (.array 0) (.literal 0) .input .byte .inline)))
  ensure (plan [.action (.bytes (.toBytes (.word .input))), .loop (.single 7) [.observe .add 3 (.bytes 0) .hash]]).admitted
    "seven hashes in a loop are not admitted"

private def shapeValues : List (String × List String) := [
  ("values", ["alias:array", "alias:bytes", "array:allocated", "array:literal", "bytes", "slice"]),
  ("parts", ["concat:bytes", "concat:slice", "concat:word", "concat:zeros", "to_bytes:bytes", "to_bytes:slice",
    "to_bytes:word", "to_bytes:zeros"]),
  ("cuts", ["drop:bytes", "drop:slice", "take:bytes", "take:slice", "window:bytes", "window:slice"]),
  ("writes", ["array:helper", "array:inline", "bytes:byte:helper", "bytes:byte:inline", "bytes:word:helper",
    "bytes:word:inline", "slice:byte:helper", "slice:byte:inline", "slice:word:helper", "slice:word:inline"]),
  ("observations", ["byte:bytes", "byte:slice", "element:get", "element:index", "hash:bytes", "hash:slice",
    "length:bytes", "length:slice", "word:bytes", "word:slice"]),
  ("indices", ["byte:counter", "byte:input", "byte:literal", "element:counter", "element:input", "element:literal",
    "put8:counter", "put8:input", "put8:literal", "put:counter", "put:input", "put:literal", "set:counter",
    "set:input", "set:literal", "word:counter", "word:input", "word:literal"]),
  ("hazards", ["alias", "copy", "helper", "view"]),
  ("loops", ["nested:counter", "nested:input", "none", "single:1", "single:3", "single:7"]),
  ("body", ["array", "bytes", "observe", "slice", "write"]),
  ("hashes", ["0", "1-31", "128", "32", "33-63", "64", "65-95", "96", "97-127"])]

/-- Generation is deterministic, its accepted plans draw every shape within
1,000 seeds, it replays exactly and drops steps to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 1000 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (MemoryValues.planJson plan == MemoryValues.planJson (generate (UInt64.ofNat (seed + 1))))
      "generation is not deterministic"
    if let .ok checked := MemoryValues.generatedPlan (Seed.ofNat (seed + 1)) MemoryValues.defaultNodes then
      if (MemoryValues.inputSensitive checked fuel).isOk then
        for (dimension, values) in checked.plan.shapes do
          for value in values do
            ensure ((shapeValues.lookup dimension).any (·.contains value)) s!"unknown shape {dimension}:{value}"
            unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"1,000 seeds never drew {dimension}:{value}"
  let corpus := MemoryValues.generateCases (Seed.ofNat 1) MemoryValues.defaultNodes 64 64 fuel
  let all ← cases corpus
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  let mut reverted := 0
  for case in all do
    ensure ((← expect (MemoryValues.replayCase case fuel)) == case) "a generated case failed exact replay"
    let direct ← expect (case.getObjVal? "directCore")
    if (direct.getObjValAs? String "status").toOption == some "reverted" then
      ensure ((direct.getObjValAs? String "output").toOption == some "0xb4120f14") "a reverted case has other data"
      reverted := reverted + 1
  ensure (reverted ≥ 8) "fewer than eight of 64 generated cases were out of range"
  let seeded ← cases (MemoryValues.generateCases (Seed.ofNat 7) MemoryValues.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← expect (MemoryValues.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 60 do
    if let .ok small := MemoryValues.generatedPlan (Seed.ofNat (seed + 1)) MemoryValues.minimumNodes then
      ensure (small.plan.budgetNodes ≤ MemoryValues.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.steps.length < (generate (UInt64.ofNat (seed + 1))).steps.length then dropped := true
  ensure dropped "a 256-node budget never dropped a step"

/-- What a reduction changed, from the first step that differs. -/
private def reductionKind (previous next : Plan) (inputChanged : Bool) : String :=
  if inputChanged then "input"
  else if next.steps.length < previous.steps.length then "step"
  else match (previous.steps.zip next.steps).find? (fun (before, after) => before != after) with
    | some (.loop shape actions, .loop shape' actions') =>
        if actions'.length < actions.length then "body"
        else if shape != shape' then "loop"
        else match (actions.zip actions').find? (fun (before, after) => before != after) with
          | some (before, after) => actionKind before after
          | none => "none"
    | some (.action before, .action after) => actionKind before after
    | _ => "none"
where
  actionKind : Action → Action → String
    | .write _ index value _ form, .write _ index' value' _ form' =>
        if form != form' then "write" else if index != index' then "index" else if value != value' then "word" else "none"
    | .observe fold constant _ access, .observe fold' constant' _ access' =>
        if fold != fold' || constant != constant' then "fold"
        else match access, access' with
          | .word index, .word index' | .byte index, .byte index' => if index != index' then "index" else "none"
          | .element index get, .element index' get' =>
              if get != get' then "access" else if index != index' then "index" else "none"
          | _, _ => "access"
    | .bytes _, .bytes _ => "build"
    | .slice .., .slice .. => "cut"
    | .array .., .array .. => "array"
    | _, _ => "none"

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, every kind applies, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (MemoryValues.generateCases (Seed.ofNat 1) MemoryValues.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← expect (case.getObjVal? "memoryValuePlan")
  ensure (MemoryValues.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (MemoryValues.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (MemoryValues.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-memory-values-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (MemoryValues.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "memoryValueShapes" (Json.mkObj []))) fuel matches .error _) "changed memory value shapes replayed"
  ensure (MemoryValues.replayCase (case.setObjVal! "memoryValuePlan" (plan.setObjVal! "steps" (.arr #[]))) fuel
    matches .error _) "a plan without steps replayed"
  ensure (MemoryValues.replayCase (case.setObjVal! "schema" (toJson "solcore-lean.semantic-memory-value-case.v0")) fuel
    matches .error _) "a changed case schema replayed"
  ensure (MemoryValues.replayCase (case.setObjVal! "directCore" (Json.mkObj [("stage", toJson "execution"),
      ("status", toJson "returned"), ("word", toJson "7")])) fuel matches .ok _)
    "replay read the saved observation"
  let origin ← expect ((← provenance case).getObjVal? "origin")
  ensure (MemoryValues.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let fixture := MemoryValues.planJson fixturePlan
  let some fixtureChecked := MemoryValues.CheckedPlan.ofPlan? fixturePlan
    | throw (IO.userError "the fixture failed the checker")
  let fixtureCase := MemoryValues.makeCase fixtureChecked (Word.ofNatModulo 5)
    (MemoryValues.emit fixturePlan) (Json.mkObj [("kind", toJson "imported")]) fuel
  ensure ((← expect (MemoryValues.replayCase fixtureCase fuel)) == fixtureCase) "the imported fixture case failed replay"
  let steps ← expect (fixture.getObjValAs? (Array Json) "steps")
  let loop := steps[8]!
  let changedLoop := loop.setObjVal! "loop" (MemoryValues.loopJson (.nested 1 .counter 3))
  ensure (MemoryValues.replayCase (fixtureCase.setObjVal! "memoryValuePlan" (fixture.setObjVal! "steps" (.arr (steps.set! 8 changedLoop)))) fuel
    matches .error _) "a changed loop replayed against the saved reference"
  let shrunk ← expect (MemoryValues.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← expect (MemoryValues.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← expect (MemoryValues.caseProgram case)
  for reduction in MemoryValues.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  let sources := (MemoryValues.CheckedPlan.ofPlan? fixturePlan).toList ++ (List.range 40).filterMap fun seed =>
    (MemoryValues.generatedPlan (Seed.ofNat (seed + 1)) MemoryValues.defaultNodes).toOption
  for checked in sources do
    let source : MemoryValues.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
    for reduction in MemoryValues.reductions source do
      let kind := reductionKind checked.plan reduction.candidate.plan.plan (reduction.candidate.input != source.input)
      unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["step", "body", "loop", "word", "index", "build", "cut", "array", "write", "access", "fold", "input"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in the fixture and 40 plans"
  let reducedOrigin ← expect ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (MemoryValues.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← expect (reduced[0]!.getObjVal? "memoryValuePlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceMemoryValuesCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceMemoryValuesCases
