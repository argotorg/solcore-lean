import Solcore.Synthesis.Source.MemoryCallsCases
import Solcore.Abi.Keccak256

/-! The `runtime-memory-calls` profile. Its Core reference inlines every call
into `runtime-memory-values`' byte-list model; it agrees with a direct
interpreter that runs each helper as a function over byte lists, with std's
range checks and `Solcore.Abi`'s Keccak-256, on generated plans, and two
fixtures' sources and results are golden, the results from a separate Python
model. Admission refuses helpers, steps, arguments, indices and counts
outside the profile; generation draws every shape and replays exactly;
tampering is refused, and reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceMemoryCallsCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.MemoryCalls
open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Fold Width Action Access)
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
length, and each helper run as a function of its argument, its index and its
Word, calling the helper it names, so that a returned argument, view, copy or
pair is what the helper's body makes of it. Writes update the store, and data
values and closures hold what their variable named. It shares no code with
the Core reference. -/

private abbrev Entry := Nat × Nat × Nat

/-- What a helper takes or returns, and what a data variable holds. -/
private inductive Val where
  | word (value : Nat)
  | memory (kind : String) (entry : Entry)
  | pair (entry : Entry) (word : Nat)
  | inl (entry : Entry)
  | inr (word : Nat)
  | first (entry : Entry) (word : Nat)
  | second (word : Nat)
  deriving Inhabited

private structure Machine where
  input : Nat
  values : Array (Array Nat) := #[]
  vars : List ((String × Nat) × Entry) := []
  counts : List (String × Nat) := []
  acc : Nat := 0
  pairs : Array Val := #[]
  sums : Array Val := #[]
  enums : Array Val := #[]
  closures : Array (Entry × Obs) := #[]

/-- The only failure of an admitted plan is an out-of-range access. -/
private abbrev Interp := StateT Machine (Except String)

private def outOfRange {α : Type} : Interp α := throw "out of range"

private def operand (value : Operand) : Interp Nat := do
  let machine ← getThe Machine
  match value with
  | .input => return machine.input
  | .add constant => return (machine.input + constant) % modulus
  | .mul constant => return (machine.input * constant) % modulus
  | .xor constant => return machine.input ^^^ constant
  | .acc => return machine.acc
  | .counter => throw "a position outside a loop"

private def index (value : Index) : Interp Nat := do
  match value with
  | .literal literal => return literal
  | .input shift divisor => return ((← getThe Machine).input >>> shift) % divisor
  | .counter .. => throw "a position outside a loop"

private def key : Ref → String × Nat
  | .bytes number => ("bytes", number)
  | .slice number => ("slice", number)
  | .array number => ("array", number)

private def declare (kind : String) (entry : Entry) : Interp Unit := modify fun machine =>
  let number := (machine.counts.lookup kind).getD 0
  {machine with vars := ((kind, number), entry) :: machine.vars,
                counts := (kind, number + 1) :: machine.counts.filter (·.1 != kind)}

private def entryOf (ref : Ref) : Interp Entry := do
  match (← getThe Machine).vars.lookup (key ref) with
  | some entry => return entry
  | none => throw "a variable out of scope"

private def bytesOf (entry : Entry) : Interp (List Nat) := do
  let (value, start, length) := entry
  return (((← getThe Machine).values[value]!).toList.drop start).take length

private def wordBytes (value : Nat) : List Nat := (List.range 32).map fun index => (value / 256 ^ (31 - index)) % 256

private def bigEndian (bytes : List Nat) : Nat := bytes.foldl (fun total byte => total * 256 + byte) 0

private def keccak (bytes : List Nat) : Nat :=
  bigEndian ((Solcore.Abi.V1.Keccak256.hash (bytes.map UInt8.ofNat).toByteArray).toList.map (·.toNat))

/-- `slice_(v, i)` then `truncate(·, width)`. -/
private def check (length position width : Nat) : Interp Unit :=
  if position > length || length - position < width then outOfRange else pure ()

private def store (value : Nat) (update : Array Nat → Array Nat) : Interp Unit := modify fun machine =>
  {machine with values := machine.values.modify value update}

private def create (data : List Nat) : Interp Nat := do
  let value := (← getThe Machine).values.size
  modify fun machine => {machine with values := machine.values.push data.toArray}
  return value

private def observeEntry (entry : Entry) (obs : Obs) (offset : Nat) : Interp Nat := do
  let (value, start, length) := entry
  match obs with
  | .length => return length
  | .hash => return keccak (← bytesOf entry)
  | .word =>
      check length offset 32
      return bigEndian ((((← getThe Machine).values[value]!).toList.drop (start + offset)).take 32)
  | .byte =>
      check length offset 1
      return ((← getThe Machine).values[value]!)[start + offset]!
  | .element =>
      if offset ≥ length then outOfRange
      return ((← getThe Machine).values[value]!)[start + offset]!

private def putEntry (entry : Entry) (offset word : Nat) : Width → Interp Unit
  | .word => do
      let (value, start, length) := entry
      check length offset 32
      store value fun bytes => (wordBytes word).zipIdx.foldl (fun bytes (byte, k) => bytes.set! (start + offset + k) byte) bytes
  | .byte => do
      let (value, start, length) := entry
      check length offset 1
      store value (·.set! (start + offset) (word % 256))

private def putElement (entry : Entry) (offset word : Nat) : Interp Unit := do
  let (value, start, length) := entry
  if offset ≥ length then outOfRange
  store value (·.set! (start + offset) word)

private def accumulate (fold : Fold) (constant observed : Nat) : Interp Unit := modify fun machine =>
  let scaled := (machine.acc * constant) % modulus
  {machine with acc := match fold with
    | .add => (scaled + observed) % modulus
    | .xor => scaled ^^^ observed}

private def combine (fold : Fold) (left right : Nat) : Nat :=
  match fold with
  | .add => (left + right) % modulus
  | .xor => left ^^^ right

private def observation : Access → Obs × Option Index
  | .length => (.length, none)
  | .hash => (.hash, none)
  | .word position => (.word, some position)
  | .byte position => (.byte, some position)
  | .element position _ => (.element, some position)

private def partBytes : Solcore.Synthesis.Core.MemoryValues.Part → Interp (List Nat)
  | .word value => do return wordBytes (← operand value)
  | .zeros count => return List.replicate count 0
  | .value ref => do bytesOf (← entryOf ref)

/-- `runtime-memory-values`' actions, outside loops. -/
private def act : Action → Interp Unit
  | .bytes build => do
      let parts := match build with
        | .toBytes single => [single]
        | .concat left right => [left, right]
      let mut data : List Nat := []
      for single in parts do
        data := data ++ (← partBytes single)
      declare "bytes" ((← create data), 0, data.length)
  | .slice source cut => do
      let (value, start, length) ← entryOf source
      declare "slice" (match cut with
        | .drop dropped => (value, start + dropped, length - dropped)
        | .take kept => (value, start, kept)
        | .window dropped kept => (value, start + dropped, kept))
  | .alias source => do declare (key source).1 (← entryOf source)
  | .array _ elements => do
      let words ← elements.mapM operand
      declare "array" ((← create words), 0, words.length)
  | .write target position written width _ => do
      let entry ← entryOf target
      let offset ← index position
      let word ← operand written
      if target.isArray then putElement entry offset word else putEntry entry offset word width
  | .observe fold constant value observed => do
      let entry ← entryOf value
      let (obs, position) := observation observed
      let offset ← match position with
        | some position => index position
        | none => pure 0
      accumulate fold constant (← observeEntry entry obs offset)

/-- Helper `number`'s body on its argument: a Word, or the value it returns. -/
private def callHelper (helpers : List Helper) : Nat → Nat → Val → Nat → Nat → Interp Val
  | 0, _, _, _, _ => throw "a chain of calls too deep"
  | fuel + 1, number, argument, offset, word => do
      let some helper := helpers[number]? | throw "a call of a missing helper"
      match helper.kind, argument with
      | .read obs fold, .memory _ entry => return .word (combine fold (← observeEntry entry obs offset) word)
      | .write width, .memory kind entry => do
          if kind == "array" then putElement entry offset word else putEntry entry offset word width
          return argument
      | .view start, .memory _ (value, first, length) => return .memory "slice" (value, first + start, length - start)
      | .copy, .memory _ entry => do
          let data := (← bytesOf entry) ++ wordBytes word
          return .memory "bytes" ((← create data), 0, data.length)
      | .call callee constant, _ => callHelper helpers fuel callee argument offset ((word + constant) % modulus)
      | .pack constant, .memory _ entry => return .pair entry ((word + constant) % modulus)
      | .take obs fold written, .pair entry carried | .take obs fold written, .first entry carried => do
          if written then putEntry entry offset carried .byte
          return .word (combine fold (← observeEntry entry obs offset) word)
      | .take obs fold written, .inl entry => do
          if written then putEntry entry offset word .byte
          return .word (combine fold (← observeEntry entry obs offset) word)
      | .take _ fold _, .inr carried | .take _ fold _, .second carried => return .word (combine fold carried word)
      | _, _ => throw "a helper took an argument it does not take"

private def argument (arg : Arg) : Interp Val := do
  let machine ← getThe Machine
  match arg with
  | .value ref => return .memory (key ref).1 (← entryOf ref)
  | .pair number => return machine.pairs[number]!
  | .sum number => return machine.sums[number]!
  | .enum number => return machine.enums[number]!

private def step (helpers : List Helper) : Step → Interp Unit
  | .action single => act single
  | .call helper arg position word _ fold constant => do
      let returned ← callHelper helpers (maximumHelpers + 1) helper (← argument arg) (← index position) (← operand word)
      match returned with
      | .word value => accumulate fold constant value
      | .memory kind entry => declare kind entry
      | .pair .. => modify fun machine => {machine with pairs := machine.pairs.push returned}
      | _ => throw "a helper returned a sum or an enum"
  | .data datum => do
      match datum with
      | .pair ref word =>
          let held := Val.pair (← entryOf ref) (← operand word)
          modify fun machine => {machine with pairs := machine.pairs.push held}
      | .inl ref =>
          let held := Val.inl (← entryOf ref)
          modify fun machine => {machine with sums := machine.sums.push held}
      | .inr word =>
          let held := Val.inr (← operand word)
          modify fun machine => {machine with sums := machine.sums.push held}
      | .first ref word =>
          let held := Val.first (← entryOf ref) (← operand word)
          modify fun machine => {machine with enums := machine.enums.push held}
      | .second word =>
          let held := Val.second (← operand word)
          modify fun machine => {machine with enums := machine.enums.push held}
  | .closure ref obs => do
      let entry ← entryOf ref
      modify fun machine => {machine with closures := machine.closures.push (entry, obs)}
  | .apply number position fold constant => do
      let (entry, obs) := (← getThe Machine).closures[number]!
      accumulate fold constant (← observeEntry entry obs (← index position))

/-- The returned Word, or `none` for an out-of-range access. -/
private def interpret (plan : Plan) (input : Nat) : Option (Option Nat) :=
  match ((plan.steps.forM (step plan.helpers)).run {input}) with
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
    match MemoryCalls.generatedPlan (Seed.ofNat (seed + 1)) MemoryCalls.defaultNodes with
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

/-! Two fixtures. The first writes a byte through a generic helper at a bytes
value and, through a function value of a generic helper that calls it, at a
slice of it, captures the returned value in a closure, takes an enum holding
the value apart with a written byte and a hash, applies the closure after the
writes, takes the enum's Word arm and observes the returned slice's length.
The second packs a bytes value into a pair through a function value, copies a
window of it, takes the packed pair apart with a written byte at an input
index, hashes the copy, takes a pair holding the copy, and reads a byte of
the window. -/

private def fixtureA : Plan := {
  helpers := [
    {param := .generic, kind := .write .byte},
    {param := .enum, kind := .take .hash .xor true},
    {param := .generic, kind := .call 0 5}],
  steps := [
    .action (.bytes (.concat (.word .input) (.word (.mul 3)))),
    .action (.slice (.bytes 0) (.drop 16)),
    .call 0 (.value (.bytes 0)) (.literal 3) (.add 7) .direct .add 3,
    .call 2 (.value (.slice 0)) (.input 1 50) .input .value .add 3,
    .closure (.bytes 1) .word,
    .data (.first (.bytes 0) (.xor 9)),
    .call 1 (.enum 0) (.literal 5) .input .direct .add 7,
    .apply 0 (.input 3 40) .xor 3,
    .data (.second (.add 2)),
    .call 1 (.enum 1) (.literal 0) (.mul 11) .direct .xor 5,
    .action (.observe .add 9 (.slice 1) .length)]}

private def fixtureB : Plan := {
  helpers := [
    {param := .bytes, kind := .pack 9},
    {param := .pair, kind := .take .byte .add true},
    {param := .slice, kind := .copy}],
  steps := [
    .action (.bytes (.concat (.word .input) (.zeros 8))),
    .call 0 (.value (.bytes 0)) (.literal 0) (.add 1) .value .add 3,
    .action (.slice (.bytes 0) (.window 4 30)),
    .call 2 (.value (.slice 0)) (.literal 0) (.xor 77) .direct .add 3,
    .call 1 (.pair 0) (.input 0 44) (.mul 3) .direct .xor 13,
    .action (.observe .add 5 (.bytes 1) .hash),
    .data (.pair (.bytes 1) .acc),
    .call 1 (.pair 1) (.literal 61) .input .direct .add 3,
    .action (.observe .xor 7 (.slice 0) (.byte (.input 8 31)))]}

/-- From the Python model of `Tests/scripts/test-semantic-memory-call-corpus.py`;
`none` is an out-of-range access. -/
private def fixtureAResults : List (Nat × Option Nat) := [
  (0, some 72242028008843834408630760672861491772646845153315677968046753082743170501259),
  (1, some 28794986706600237396589248746379040974034525714432669763486185533587286561136),
  (2, some 16511079347741181052288917318141561912842708339331099409325098332830202613987),
  (255, some 107535809238064730873335995143676968170243187874906453889788097605332025595584),
  (256, some 70515616853955502638081244769189250539733285920752415866804593287428544386072),
  (2 ^ 256 - 1, some 57655881719293170964465309150860510537028812815812853729182389455680009867045),
  (2 ^ 255, some 33261368517523964077741793340843518474846216834467566246152698697055181055799),
  (2 ^ 255 - 1, some 39200207660929337112266666871390544428014184820884090925102396269974450162141),
  (3, some 39550463219767020936447378244865110222821850776900421484745546207258526633877),
  (99, none),
  (300, none),
  (1001, some 60830111377926786314490136554414777589416998269549332393809054047616830022487)]

private def fixtureBResults : List (Nat × Option Nat) := [
  (0, some 70895379005827235410385788254663289791512939887124188183065356754751538211480),
  (1, some 26555323344963878524516092858499067571302160062675108872867170230023276099303),
  (2, some 104699478716185010130315260041630595032925429523647116161313331864302840415402),
  (255, some 64977749603918774623399018940398306120938914228916938263254806947498849643353),
  (256, some 22785389816243773430335715020161494851259740866219976544483484395265919071376),
  (2 ^ 256 - 1, some 18758776471704661775015560766960060675843703994723565537355641480988536135938),
  (2 ^ 255, some 39800692868954229084531459478632215291755259371103084633425376066695511368604),
  (2 ^ 255 - 1, some 17342871063904328424333649282263394694054430976925053944197056639101938932778),
  (3, some 54611389255892579513659646500361393792497290255370143099917570726769428808481),
  (42, none),
  (7680, none),
  (1001, some 101271697361168520248805485127094807716825221348644557259711928758180779855971)]

private def header : List String := [
  "import * from std;",
  "import * from std.dispatch;",
  "import { mload, mstore, mstore8, shr, mod } from std.opcodes;",
  ""]

private def fixtureASource : String := String.intercalate "\n" (header ++ [
  "function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
  "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));",
  "}",
  "",
  "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
  "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);",
  "}",
  "",
  "enum Sc_E {",
  "    Sc_E0(memory<bytes>, word),",
  "    Sc_E1(word)",
  "}",
  "",
  "function sc_h0<a>(sc_v: a, sc_i: word, sc_w: word) returns (a) where a: MemorySize, a: MemoryPointer, a: MemoryEncode {",
  "    sc_put8(sc_v, sc_i, sc_w);",
  "    return sc_v;",
  "}",
  "",
  "function sc_h1(sc_v: Sc_E, sc_i: word, sc_w: word) returns (word) {",
  "    match (sc_v) {",
  "        case Sc_E.Sc_E0(sc_p, sc_q) {",
  "            sc_put8(sc_p, sc_i, sc_q);",
  "            return (Typedef.rep(keccak256_(sc_p)) ^ sc_w);",
  "        }",
  "        case Sc_E.Sc_E1(sc_q) {",
  "            return (sc_q ^ sc_w);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_h2<a>(sc_v: a, sc_i: word, sc_w: word) returns (a) where a: MemorySize, a: MemoryPointer, a: MemoryEncode {",
  "    return sc_h0(sc_v, sc_i, (sc_w + 5));",
  "}",
  "",
  "contract SynthesizedMemoryCalls {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = concat(bytes32(sc_x), bytes32((sc_x * 3)));",
  "        let sc_s0: memory_ref = slice_(sc_b0, 16);",
  "        let sc_b1: memory<bytes> = sc_h0(sc_b0, 3, (sc_x + 7));",
  "        let sc_f0: function (memory_ref, word, word) returns (memory_ref) = sc_h2;",
  "        let sc_s1: memory_ref = sc_f0(sc_s0, mod(shr(1, sc_x), 50), sc_x);",
  "        let sc_c0: function (word) returns (word) = lam (sc_j: word) -> word {",
  "            return sc_word(sc_b1, sc_j);",
  "        };",
  "        let sc_e0: Sc_E = Sc_E.Sc_E0(sc_b0, (sc_x ^ 9));",
  "        sc_r = ((sc_r * 7) + sc_h1(sc_e0, 5, sc_x));",
  "        sc_r = ((sc_r * 3) ^ sc_c0(mod(shr(3, sc_x), 40)));",
  "        let sc_e1: Sc_E = Sc_E.Sc_E1((sc_x + 2));",
  "        sc_r = ((sc_r * 5) ^ sc_h1(sc_e1, 0, (sc_x * 11)));",
  "        sc_r = ((sc_r * 9) + MemorySize.len(sc_s1));",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureBSource : String := String.intercalate "\n" (header ++ [
  "function sc_byte<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
  "    return shr(248, mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1))));",
  "}",
  "",
  "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
  "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);",
  "}",
  "",
  "function sc_h0(sc_v: memory<bytes>, sc_i: word, sc_w: word) returns ((memory<bytes>, word)) {",
  "    return (sc_v, (sc_w + 9));",
  "}",
  "",
  "function sc_h1(sc_v: (memory<bytes>, word), sc_i: word, sc_w: word) returns (word) {",
  "    match (sc_v) {",
  "        case (sc_p, sc_q) {",
  "            sc_put8(sc_p, sc_i, sc_q);",
  "            return (sc_byte(sc_p, sc_i) + sc_w);",
  "        }",
  "    }",
  "}",
  "",
  "function sc_h2(sc_v: memory_ref, sc_i: word, sc_w: word) returns (memory<bytes>) {",
  "    return concat(sc_v, bytes32(sc_w));",
  "}",
  "",
  "contract SynthesizedMemoryCalls {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = concat(bytes32(sc_x), empty(8));",
  "        let sc_f0: function (memory<bytes>, word, word) returns ((memory<bytes>, word)) = sc_h0;",
  "        let sc_t0: (memory<bytes>, word) = sc_f0(sc_b0, 0, (sc_x + 1));",
  "        let sc_s0: memory_ref = truncate(slice_(sc_b0, 4), 30);",
  "        let sc_b1: memory<bytes> = sc_h2(sc_s0, 0, (sc_x ^ 77));",
  "        sc_r = ((sc_r * 13) ^ sc_h1(sc_t0, mod(shr(0, sc_x), 44), (sc_x * 3)));",
  "        sc_r = ((sc_r * 5) + Typedef.rep(keccak256_(sc_b1)));",
  "        let sc_t1: (memory<bytes>, word) = (sc_b1, sc_r);",
  "        sc_r = ((sc_r * 3) + sc_h1(sc_t1, 61, sc_x));",
  "        sc_r = ((sc_r * 7) ^ sc_byte(sc_s0, mod(shr(8, sc_x), 31)));",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureAShapes : List (String × List String) := [
  ("helpers", ["call:generic", "take:enum", "write:generic"]),
  ("calls", ["direct:bytes", "direct:word", "value:slice"]),
  ("passes", []),
  ("instances", ["bytes", "several", "slice"]),
  ("data", ["enum0", "enum1"]),
  ("closures", ["word:bytes"]),
  ("observations", ["carried:enum", "hash:enum"]),
  ("indices", ["put8:input", "put8:literal", "word:input"]),
  ("ranges", ["apply", "call"]),
  ("hazards", ["alias", "closure", "helper"]),
  ("steps", ["action:bytes", "action:observe", "action:slice", "apply", "call", "closure", "data"])]

private def fixtureBShapes : List (String × List String) := [
  ("helpers", ["copy:slice", "pack:bytes", "take:pair"]),
  ("calls", ["direct:bytes", "direct:word", "value:pair"]),
  ("passes", ["pair"]),
  ("instances", []),
  ("data", ["pair"]),
  ("closures", []),
  ("observations", ["byte:pair"]),
  ("indices", ["byte:input", "byte:literal", "put8:input", "put8:literal"]),
  ("ranges", ["call"]),
  ("hazards", ["alias", "copy", "helper"]),
  ("steps", ["action:bytes", "action:observe", "action:slice", "call", "data"])]

private def fixtureChecks : IO Unit := do
  for (label, plan, source, results, shapes) in [
      ("first", fixtureA, fixtureASource, fixtureAResults, fixtureAShapes),
      ("second", fixtureB, fixtureBSource, fixtureBResults, fixtureBShapes)] do
    ensure plan.admitted s!"the {label} fixture plan is not admitted"
    let some checked := MemoryCalls.CheckedPlan.ofPlan? plan
      | throw (IO.userError s!"the {label} fixture failed the checker")
    ensure ((MemoryCalls.emit plan).source == source) s!"the {label} fixture source changed"
    for (value, expected) in results do
      ensure ((← run (checked.program (Word.ofNatModulo value))) == expected) s!"{label} fixture input {value}: Core result"
      ensure (interpret plan value == some expected) s!"{label} fixture input {value}: interpreter result"
    ensure (plan.shapes == shapes) s!"the {label} fixture shapes changed"
    ensure (match MemoryCalls.planOf (MemoryCalls.planJson plan) with
      | .ok decoded => decoded == plan
      | .error _ => false) s!"the {label} fixture plan JSON does not round-trip"
  let some checked := MemoryCalls.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  ensure (MemoryCalls.observe checked (Word.ofNatModulo 99) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0xb4120f14")])
    "an out-of-range access in a helper is not observed as std's OutOfBounds() revert"

private def withStep (plan : Plan) (index : Nat) (replacement : Step) : Plan :=
  {plan with steps := plan.steps.set index replacement}

private def withHelper (plan : Plan) (index : Nat) (replacement : Helper) : Plan :=
  {plan with helpers := plan.helpers.set index replacement}

/-- Admission refuses what the compiler or the reference cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let bytes := Step.action (.bytes (.concat (.word .input) (.word .input)))
  let observe := Step.action (.observe .add 3 (.bytes 0) .length)
  let lengthOf := fun (param : Param) => ({param, kind := .read .length .add} : Helper)
  let readCall := fun (arg : Arg) => Step.call 0 arg (.literal 0) .input .direct .add 3
  let single := fun (helper : Helper) (steps : List Step) => ({helpers := [helper], steps} : Plan)
  let double := fun (first second : Helper) (steps : List Step) => ({helpers := [first, second], steps} : Plan)
  let a := fixtureA
  let b := fixtureB
  refused "no helper" ({a with helpers := []} : Plan)
  refused "four helpers" ({a with helpers := a.helpers ++ [lengthOf .bytes]} : Plan)
  refused "no step" ({a with steps := []} : Plan)
  refused "thirteen steps" ({a with steps := a.steps ++ [observe, observe]} : Plan)
  refused "no call" (single (lengthOf .bytes) [bytes, observe])
  refused "no observation" (single {param := .bytes, kind := .write .word}
    [bytes, .call 0 (.value (.bytes 0)) (.literal 0) .input .direct .add 3])
  refused "a helper calling itself" (single {param := .bytes, kind := .call 0 1} [bytes, readCall (.value (.bytes 0))])
  refused "a helper calling a later one" (double {param := .bytes, kind := .call 1 1} (lengthOf .bytes)
    [bytes, readCall (.value (.bytes 0))])
  refused "a callee of another parameter" (double (lengthOf .bytes) {param := .slice, kind := .call 0 1}
    [bytes, .action (.slice (.bytes 0) (.drop 0)), .call 1 (.value (.slice 0)) (.literal 0) .input .direct .add 3])
  refused "a call constant of 0" (withHelper a 2 {param := .generic, kind := .call 0 0})
  refused "a call constant of 256" (withHelper a 2 {param := .generic, kind := .call 0 256})
  refused "a view from 33" (single {param := .bytes, kind := .view 33} [bytes,
    .call 0 (.value (.bytes 0)) (.literal 0) .input .direct .add 3, .action (.observe .add 3 (.slice 0) .length)])
  refused "a pack of a slice" (withHelper b 0 {param := .slice, kind := .pack 9})
  refused "a pack constant of 0" (withHelper b 0 {param := .bytes, kind := .pack 0})
  refused "a take of a bytes value" (single {param := .bytes, kind := .take .length .add false} [bytes, readCall (.value (.bytes 0))])
  refused "an element of bytes" (single {param := .bytes, kind := .read .element .add} [bytes, readCall (.value (.bytes 0))])
  refused "a take of an element" (withHelper b 1 {param := .pair, kind := .take .element .add true})
  refused "the length of an array" (single (lengthOf .array) [.action (.array false [.input]), readCall (.value (.array 0))])
  refused "a byte write to an array" (single {param := .array, kind := .write .byte} [.action (.array false [.input]),
    .call 0 (.value (.array 0)) (.literal 0) .input .direct .add 3, .action (.observe .add 3 (.array 0) (.element (.literal 0) false))])
  refused "a copy of an array" (single {param := .array, kind := .copy} [.action (.array false [.input]),
    .call 0 (.value (.array 0)) (.literal 0) .input .direct .add 3, observe])
  refused "a read of a pair" (single (lengthOf .pair) [bytes, .data (.pair (.bytes 0) .input), readCall (.pair 0)])
  refused "a slice to a bytes parameter" (single (lengthOf .bytes) [bytes, .action (.slice (.bytes 0) (.drop 0)),
    readCall (.value (.slice 0))])
  refused "an array to a generic parameter" (single (lengthOf .generic) [.action (.array false [.input]),
    readCall (.value (.array 0))])
  refused "a sum to a pair parameter" (withStep b 4 (.call 1 (.sum 0) (.input 0 44) (.mul 3) .direct .xor 13))
  refused "an undeclared argument" (single (lengthOf .bytes) [bytes, readCall (.value (.bytes 5))])
  refused "a missing pair" (withStep b 4 (.call 1 (.pair 3) (.input 0 44) (.mul 3) .direct .xor 13))
  refused "an unused index of 1" (single (lengthOf .bytes) [bytes, .call 0 (.value (.bytes 0)) (.literal 1) .input .direct .add 3])
  refused "a literal index past the end" (withStep a 2 (.call 0 (.value (.bytes 0)) (.literal 64) (.add 7) .direct .add 3))
  refused "a modulus nine past the positions" (withStep a 3 (.call 2 (.value (.slice 0)) (.input 1 57) .input .value .add 3))
  refused "an unlisted shift" (withStep a 3 (.call 2 (.value (.slice 0)) (.input 2 50) .input .value .add 3))
  refused "a position index in a call" (withStep a 2 (.call 0 (.value (.bytes 0)) (.counter 1 0) (.add 7) .direct .add 3))
  refused "a position Word in a call" (withStep a 2 (.call 0 (.value (.bytes 0)) (.literal 3) .counter .direct .add 3))
  refused "a value result folded by ^" (withStep a 2 (.call 0 (.value (.bytes 0)) (.literal 3) (.add 7) .direct .xor 3))
  refused "a value result with constant 5" (withStep a 2 (.call 0 (.value (.bytes 0)) (.literal 3) (.add 7) .direct .add 5))
  refused "an even fold constant" (withStep a 6 (.call 1 (.enum 0) (.literal 5) .input .direct .add 4))
  refused "an added zero" (withStep a 2 (.call 0 (.value (.bytes 0)) (.literal 3) (.add 0) .direct .add 3))
  refused "a copy past 128 bytes" (single {param := .bytes, kind := .copy} [bytes,
    .action (.bytes (.concat (.value (.bytes 0)) (.zeros 33))), .call 0 (.value (.bytes 1)) (.literal 0) .input .direct .add 3, observe])
  refused "a view past the end" (single {param := .bytes, kind := .view 20} [.action (.bytes (.toBytes (.zeros 16))),
    .call 0 (.value (.bytes 0)) (.literal 0) .input .direct .add 3, .action (.observe .add 3 (.slice 0) .length)])
  refused "a third pair" ({b with steps := b.steps.take 7 ++ [.data (.pair (.bytes 0) .input)] ++ b.steps.drop 7} : Plan)
  refused "a third sum" (single (lengthOf .bytes) [bytes, .data (.inl (.bytes 0)), .data (.inr .input), .data (.inr .input),
    readCall (.value (.bytes 0))])
  refused "a third enum" (single (lengthOf .bytes) [bytes, .data (.second .input), .data (.second .input), .data (.second .input),
    readCall (.value (.bytes 0))])
  refused "a third closure" (single (lengthOf .bytes) [bytes, .closure (.bytes 0) .length, .closure (.bytes 0) .length,
    .closure (.bytes 0) .length, readCall (.value (.bytes 0))])
  refused "a fourth function value" (single (lengthOf .bytes) ([bytes] ++
    List.replicate 4 (.call 0 (.value (.bytes 0)) (.literal 0) .input .value .add 3)))
  refused "a fifth bytes value" (single {param := .bytes, kind := .copy} (List.replicate 4 (.action (.bytes (.toBytes (.word .input)))) ++
    [.call 0 (.value (.bytes 0)) (.literal 0) .input .direct .add 3, observe]))
  refused "a closure's element of bytes" (withStep a 4 (.closure (.bytes 1) .element))
  refused "a closure's length of an array" (single (lengthOf .bytes) [bytes, .action (.array false [.input]),
    .closure (.array 0) .length, readCall (.value (.bytes 0))])
  refused "an application of a missing closure" (withStep a 7 (.apply 1 (.input 3 40) .xor 3))
  refused "an application past the positions" (withStep a 7 (.apply 0 (.literal 33) .xor 3))
  refused "an unused application index of 1" (single (lengthOf .bytes) [bytes, .closure (.bytes 0) .length,
    .apply 0 (.literal 1) .add 3, readCall (.value (.bytes 0))])
  refused "inl of a slice" (single (lengthOf .bytes) [bytes, .action (.slice (.bytes 0) (.drop 0)), .data (.inl (.slice 0)),
    readCall (.value (.bytes 0))])
  refused "a pair of an array" (single (lengthOf .bytes) [bytes, .action (.array false [.input]), .data (.pair (.array 0) .input),
    readCall (.value (.bytes 0))])
  let hashing := fun (count : Nat) => single {param := .bytes, kind := .read .hash .add}
    ([bytes] ++ List.replicate count (.call 0 (.value (.bytes 0)) (.literal 0) .input .direct .add 3))
  refused "eight hashes" (hashing 8)
  ensure (hashing 7).admitted "seven hashing calls are not admitted"

private def shapeValues : List (String × List String) := [
  ("helpers", ["call:array", "call:bytes", "call:enum", "call:generic", "call:pair", "call:slice", "call:sum",
    "copy:bytes", "copy:generic", "copy:slice", "pack:bytes", "read:array", "read:bytes", "read:generic", "read:slice",
    "take:enum", "take:pair", "take:sum", "view:bytes", "view:generic", "view:slice",
    "write:array", "write:bytes", "write:generic", "write:slice"]),
  ("calls", ["direct:array", "direct:bytes", "direct:pair", "direct:slice", "direct:word",
    "value:array", "value:bytes", "value:pair", "value:slice", "value:word"]),
  ("passes", ["array", "bytes", "pair", "slice"]),
  ("instances", ["bytes", "several", "slice"]),
  ("data", ["enum0", "enum1", "inl", "inr", "pair"]),
  ("closures", ["byte:bytes", "byte:slice", "element:array", "hash:bytes", "hash:slice", "length:bytes", "length:slice",
    "word:bytes", "word:slice"]),
  ("observations", ["byte:bytes", "byte:enum", "byte:pair", "byte:slice", "byte:sum", "carried:enum", "carried:sum",
    "element:array", "hash:bytes", "hash:enum", "hash:pair", "hash:slice", "hash:sum", "length:bytes", "length:enum",
    "length:pair", "length:slice", "length:sum", "word:bytes", "word:enum", "word:pair", "word:slice", "word:sum"]),
  ("indices", ["byte:input", "byte:literal", "element:input", "element:literal", "put8:input", "put8:literal",
    "put:input", "put:literal", "set:input", "set:literal", "word:input", "word:literal"]),
  ("ranges", ["apply", "call"]),
  ("hazards", ["alias", "closure", "copy", "helper"]),
  ("steps", ["action:alias", "action:array", "action:bytes", "action:observe", "action:slice", "action:write",
    "apply", "call", "closure", "data"])]

/-- Generation is deterministic, its accepted plans draw every shape within
1,000 seeds, it replays exactly and drops steps to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 1000 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (MemoryCalls.planJson plan == MemoryCalls.planJson (generate (UInt64.ofNat (seed + 1))))
      "generation is not deterministic"
    if let .ok checked := MemoryCalls.generatedPlan (Seed.ofNat (seed + 1)) MemoryCalls.defaultNodes then
      if (MemoryCalls.inputSensitive checked fuel).isOk then
        for (dimension, values) in checked.plan.shapes do
          for value in values do
            ensure ((shapeValues.lookup dimension).any (·.contains value)) s!"unknown shape {dimension}:{value}"
            unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"1,000 seeds never drew {dimension}:{value}"
  let all ← cases (MemoryCalls.generateCases (Seed.ofNat 1) MemoryCalls.defaultNodes 64 64 fuel)
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  let mut reverted := 0
  for case in all do
    ensure ((← expect (MemoryCalls.replayCase case fuel)) == case) "a generated case failed exact replay"
    let direct ← expect (case.getObjVal? "directCore")
    if (direct.getObjValAs? String "status").toOption == some "reverted" then
      ensure ((direct.getObjValAs? String "output").toOption == some "0xb4120f14") "a reverted case has other data"
      reverted := reverted + 1
  ensure (reverted ≥ 4) "fewer than four of 64 generated cases were out of range"
  let seeded ← cases (MemoryCalls.generateCases (Seed.ofNat 7) MemoryCalls.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← expect (MemoryCalls.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 200 do
    if let .ok small := MemoryCalls.generatedPlan (Seed.ofNat (seed + 1)) MemoryCalls.minimumNodes then
      ensure (small.plan.budgetNodes ≤ MemoryCalls.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.steps.length < (generate (UInt64.ofNat (seed + 1))).steps.length then dropped := true
  ensure dropped "a 256-node budget never dropped a step"

/-- What a reduction changed, from the first helper or step that differs. -/
private def reductionKind (previous next : Plan) (inputChanged : Bool) : String :=
  if inputChanged then "input"
  else if next.helpers.length < previous.helpers.length then "helper"
  else if next.helpers != previous.helpers then
    match (previous.helpers.zip next.helpers).find? (fun (before, after) => before != after) with
    | some (before, after) => if before.param != after.param then "generic" else "kind"
    | none => "none"
  else if next.steps.length < previous.steps.length then "step"
  else if next.steps.length > previous.steps.length then "inline"
  else match (previous.steps.zip next.steps).find? (fun (before, after) => before != after) with
    | some (.call helper _ index word form fold constant, .call helper' _ index' word' form' fold' constant') =>
        if helper != helper' then "bypass" else if form != form' then "form"
        else if fold != fold' || constant != constant' then "fold" else if index != index' then "index"
        else if word != word' then "word" else "none"
    | some (.call .., .action (.write ..)) => "pass"
    | some (.call .., _) => "inline"
    | some (.action _, .action _) => "action"
    | some (.data _, .data _) => "data"
    | some (.closure .., .closure ..) => "closure"
    | some (.apply _ index fold constant, .apply _ index' fold' constant') =>
        if fold != fold' || constant != constant' then "fold" else if index != index' then "index" else "none"
    | _ => "none"

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, every kind applies, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (MemoryCalls.generateCases (Seed.ofNat 1) MemoryCalls.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← expect (case.getObjVal? "memoryCallPlan")
  ensure (MemoryCalls.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (MemoryCalls.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (MemoryCalls.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-memory-calls-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (MemoryCalls.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "memoryCallShapes" (Json.mkObj []))) fuel matches .error _) "changed memory call shapes replayed"
  ensure (MemoryCalls.replayCase (case.setObjVal! "memoryCallPlan" (plan.setObjVal! "helpers" (.arr #[]))) fuel
    matches .error _) "a plan without helpers replayed"
  ensure (MemoryCalls.replayCase (case.setObjVal! "schema" (toJson "solcore-lean.semantic-memory-call-case.v0")) fuel
    matches .error _) "a changed case schema replayed"
  ensure (MemoryCalls.replayCase (case.setObjVal! "directCore" (Json.mkObj [("stage", toJson "execution"),
      ("status", toJson "returned"), ("word", toJson "7")])) fuel matches .ok _)
    "replay read the saved observation"
  let origin ← expect ((← provenance case).getObjVal? "origin")
  ensure (MemoryCalls.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let fixture := MemoryCalls.planJson fixtureA
  let some fixtureChecked := MemoryCalls.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  let fixtureCase := MemoryCalls.makeCase fixtureChecked (Word.ofNatModulo 5)
    (MemoryCalls.emit fixtureA) (Json.mkObj [("kind", toJson "imported")]) fuel
  ensure ((← expect (MemoryCalls.replayCase fixtureCase fuel)) == fixtureCase) "the imported fixture case failed replay"
  let helpers ← expect (fixture.getObjValAs? (Array Json) "helpers")
  let changed := helpers.set! 2 (MemoryCalls.helperJson {param := .generic, kind := .call 0 6})
  ensure (MemoryCalls.replayCase (fixtureCase.setObjVal! "memoryCallPlan" (fixture.setObjVal! "helpers" (.arr changed))) fuel
    matches .error _) "a changed helper replayed against the saved reference"
  let shrunk ← expect (MemoryCalls.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← expect (MemoryCalls.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← expect (MemoryCalls.caseProgram case)
  for reduction in MemoryCalls.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  let sources := [fixtureA, fixtureB].filterMap MemoryCalls.CheckedPlan.ofPlan? ++ (List.range 40).filterMap fun seed =>
    (MemoryCalls.generatedPlan (Seed.ofNat (seed + 1)) MemoryCalls.defaultNodes).toOption
  for checked in sources do
    let source : MemoryCalls.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
    for reduction in MemoryCalls.reductions source do
      let kind := reductionKind checked.plan reduction.candidate.plan.plan (reduction.candidate.input != source.input)
      unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["step", "helper", "inline", "pass", "bypass", "generic", "kind", "form", "fold", "index", "word", "data",
      "closure", "action", "input"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in the fixtures and 40 plans"
  let reducedOrigin ← expect ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (MemoryCalls.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← expect (reduced[0]!.getObjVal? "memoryCallPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceMemoryCallsCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceMemoryCallsCases
