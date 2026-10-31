import Solcore.Synthesis.Source.RevertDataCases

/-! The `runtime-revert-data` profile. Its Core reference returns the
accumulator or the revert data of the first site whose condition decides; it
agrees with a direct interpreter that runs each helper and closure as a
function over byte lists and stops at a site with its data, on generated
plans, and two fixtures' sources and results are golden, the results from a
separate Python model. Admission refuses helpers, sites, payloads, steps and
counts outside the profile; generation draws every shape and replays
exactly; tampering is refused, and reductions are strictly smaller and
replay. -/
set_option autoImplicit false

namespace Tests.SourceRevertDataCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Operand Fold Action Part)
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

private def wordBytes (value : Nat) : List Nat := (List.range 32).map fun index => (value / 256 ^ (31 - index)) % 256

private def bigEndian (bytes : List Nat) : Nat := bytes.foldl (fun total byte => total * 256 + byte) 0

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

/-- A run's result: a returned Word, or revert data. -/
private inductive Result where
  | returned (word : Nat)
  | reverted (data : List Nat)
  deriving BEq, Repr

/-- A returned Word in decimal, revert data in hex. -/
private def Result.text : Result → String
  | .returned word => toString word
  | .reverted data => "0x" ++ String.ofList (data.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

private def run (program : Solcore.Core.Wire.Program) : IO Result :=
  match program.toCore.runStateful fuel with
  | .done (.inLeft _ (.word value)) _ => pure (.returned value.val)
  | .done (.inRight _ (.pair (.word length) (.pair (.word first) (.word second)))) _ =>
      if length.val ≤ 64 then pure (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val))
      else throw (IO.userError "a reference program reverted with more than 64 bytes")
  | _ => throw (IO.userError "a reference program returned neither a Word nor revert data")

/-! A direct interpreter of a plan: bytes values as byte lists in a store of
objects, variables naming an object, `Error` values as a selector Word,
empty, or the object a message names, so that a message's data are its
object's bytes when a site raises it, and each helper and closure run as a
function of its `Error` and Word. A site stops the run with its data. It
shares no code with the Core reference. -/

private inductive Err where
  | selector (word : Nat)
  | empty
  | message (object : Nat)
  deriving Inhabited, BEq

private structure Machine where
  input : Nat
  objects : Array (Array Nat) := #[]
  bytes : Array (Option Nat) := #[]
  errors : Array Err := #[]
  pairs : Array (Option Err × Option Nat) := #[]
  sums : Array (Option Err × Option Nat) := #[]
  enums : Array (Option Err × Option Nat) := #[]
  closures : Array (Site × Fold × Nat) := #[]
  acc : Nat := 0
  counter : Option Nat := none

private inductive Stop where
  | revert (data : List Nat)
  | fault (message : String)

private abbrev Interp := StateT Machine (Except Stop)

private def fault {α : Type} (message : String) : Interp α := throw (.fault message)

/-- A Word of `run`, or of a helper or closure whose parameter is `base`. -/
private def operand (base : Option Nat) (value : Operand) : Interp Nat := do
  let machine ← getThe Machine
  let own := base.getD machine.input
  match value with
  | .input => return own
  | .add constant => return (own + constant) % modulus
  | .mul constant => return (own * constant) % modulus
  | .xor constant => return own ^^^ constant
  | .acc => return machine.acc
  | .counter => match machine.counter with
    | some counter => return counter
    | none => fault "a counter outside a loop"

private def objectOf (value : Nat) : Interp Nat := do
  match (← getThe Machine).bytes[value]? with
  | some (some object) => return object
  | _ => fault "a bytes value out of scope"

private def contents (object : Nat) : Interp (List Nat) := do
  return (((← getThe Machine).objects[object]?).getD #[]).toList

private def dataOf : Err → Interp (List Nat)
  | .selector word => return (wordBytes word).drop 28
  | .empty => return []
  | .message object => contents object

private def made (base : Option Nat) : Make → Interp Err
  | .selector word => do return .selector (← operand base word)
  | .empty => return .empty
  | .message value => do return .message (← objectOf value)

private def origin (base : Option Nat) (param : Option Err) : Source → Interp Err
  | .make making => made base making
  | .named number => do
      match (← getThe Machine).errors[number]? with
      | some error => return error
      | none => fault "an Error variable out of scope"
  | .param => match param with
      | some error => return error
      | none => fault "no Error parameter"

private def holds (word : Nat) : Test → Bool
  | .lt constant => word < constant
  | .gt constant => word > constant
  | .eq constant => word == constant
  | .ne constant => word != constant
  | .bits mask value => word &&& mask == value

private def literalBytes (text : Nat) : List Nat := (literals.getD text "").toUTF8.toList.map (·.toNat)

/-- An `if` site raises when its condition holds, a `require` when it fails. -/
private def raiseAt (base : Option Nat) (param : Option Err) (single : Site) : Interp Unit := do
  let condition := holds (← operand base single.cond.word) single.cond.test
  if condition == (single.form == .when) then
    let data ← match single.payload with
      | .error source => do dataOf (← origin base param source)
      | .literal text => pure (literalBytes text)
      | .none => pure []
    throw (.revert data)

private def combine (fold : Fold) (left right : Nat) : Nat :=
  match fold with
  | .add => (left + right) % modulus
  | .xor => left ^^^ right

private def accumulate (fold : Fold) (constant observed : Nat) : Interp Unit := modify fun machine =>
  {machine with acc := combine fold ((machine.acc * constant) % modulus) observed}

private def partBytes : Part → Interp (List Nat)
  | .word value => do return wordBytes (← operand none value)
  | .zeros count => return List.replicate count 0
  | .value (.bytes value) => do contents (← objectOf value)
  | .value _ => fault "a part outside the profile"

/-- The profile's actions; `slot` is a loop body's own variable. -/
private def act (slot : Option Nat) : Action → Interp Unit
  | .bytes build => do
      let parts := match build with
        | .toBytes single => [single]
        | .concat left right => [left, right]
      let mut data : List Nat := []
      for single in parts do
        data := data ++ (← partBytes single)
      let object := (← getThe Machine).objects.size
      modify fun machine => {machine with objects := machine.objects.push data.toArray}
      match slot with
      | some index => modify fun machine => {machine with bytes := machine.bytes.set! index (some object)}
      | none => modify fun machine => {machine with bytes := machine.bytes.push (some object)}
  | .alias (.bytes value) => do
      let object ← objectOf value
      modify fun machine => {machine with bytes := machine.bytes.push (some object)}
  | .write (.bytes value) (.literal position) written width _ => do
      let object ← objectOf value
      let word ← operand none written
      modify fun machine => {machine with objects := machine.objects.modify object fun bytes =>
        match width with
        | .word => (wordBytes word).zipIdx.foldl (fun bytes (byte, k) => bytes.set! (position + k) byte) bytes
        | .byte => bytes.set! position (word % 256)}
  | .observe fold constant (.bytes value) access => do
      let data ← contents (← objectOf value)
      let observed ← match access with
        | .length => pure data.length
        | .word (.literal position) => pure (bigEndian ((data.drop position).take 32))
        | .byte (.literal position) => pure (data.getD position 0)
        | _ => fault "an access outside the profile"
      accumulate fold constant observed
  | _ => fault "an action outside the profile"

/-- A `raise` or `call` helper on its `Error` and Word: its result. -/
private def raiseCall (helpers : List Helper) : Nat → Nat → Err → Nat → Interp Nat
  | 0, _, _, _ => fault "a chain of calls too deep"
  | fuel + 1, number, error, word => do
      match helpers[number]? with
      | some (.call callee constant) => raiseCall helpers fuel callee error ((word + constant) % modulus)
      | some (.raise single fold constant) => do
          raiseAt (some word) (some error) single
          return combine fold word constant
      | _ => fault "a call of a helper that does not raise"

private def declared (helpers : List Helper) : Decl → Interp Err
  | .make making => made none making
  | .helper helper word => do
      match helpers[helper]? with
      | some (.make constant) => return .selector (((← operand none word) + constant) % modulus)
      | _ => fault "a made Error without a make helper"
  | .message _ value => do return .message (← objectOf value)
  | .pick helper word first second => do
      match helpers[helper]? with
      | some (.pick test) =>
          let chosen ← origin none none first
          let other ← origin none none second
          return if holds (← operand none word) test then chosen else other
      | _ => fault "a picked Error without a pick helper"

private def held (error : Option Source) (word : Option Operand) : Interp (Option Err × Option Nat) := do
  let error ← match error with
    | some source => some <$> origin none none source
    | none => pure none
  let word ← match word with
    | some value => some <$> operand none value
    | none => pure none
  return (error, word)

private def runStep (helpers : List Helper) : Step → Interp Unit
  | .action single => act none single
  | .error decl => do
      let error ← declared helpers decl
      modify fun machine => {machine with errors := machine.errors.push error}
  | .data datum => do
      match datum with
      | .pair error word => do
          let value ← held (some error) (some word)
          modify fun machine => {machine with pairs := machine.pairs.push value}
      | .inl error => do
          let value ← held (some error) none
          modify fun machine => {machine with sums := machine.sums.push value}
      | .inr word => do
          let value ← held none (some word)
          modify fun machine => {machine with sums := machine.sums.push value}
      | .first error word => do
          let value ← held (some error) (some word)
          modify fun machine => {machine with enums := machine.enums.push value}
      | .second word => do
          let value ← held none (some word)
          modify fun machine => {machine with enums := machine.enums.push value}
  | .site single => raiseAt none none single
  | .call helper error word _ fold constant => do
      let error ← origin none none error
      let result ← raiseCall helpers (maximumHelpers + 1) helper error (← operand none word)
      accumulate fold constant result
  | .take target single fold constant => do
      let machine ← getThe Machine
      let entry := match target with
        | .pair number => machine.pairs[number]?
        | .sum number => machine.sums[number]?
        | .enum number => machine.enums[number]?
      let some (error, word) := entry | fault "a data value out of scope"
      if let some error := error then raiseAt none (some error) single
      if let some word := word then accumulate fold constant word
  | .closure single fold constant => modify fun machine =>
      {machine with closures := machine.closures.push (single, fold, constant)}
  | .apply number word fold constant => do
      let some (single, own, added) := (← getThe Machine).closures[number]? | fault "a missing closure"
      let argument ← operand none word
      raiseAt (some argument) none single
      accumulate fold constant (combine own argument added)
  | .loop mask body => do
      let outer := (← getThe Machine).bytes.size
      let own := (body.filter fun item => item matches .action _).length
      modify fun machine => {machine with bytes := machine.bytes ++ (List.replicate own none).toArray}
      for counter in List.range ((← getThe Machine).input &&& mask) do
        modify fun machine => {machine with counter := some counter}
        let mut slot := outer
        for item in body do
          match item with
          | .action single =>
              act (some slot) single
              slot := slot + 1
          | .site single => raiseAt none none single
      modify fun machine =>
        {machine with counter := none, bytes := machine.bytes.extract 0 outer ++ (List.replicate own none).toArray}

/-- The returned Word or the revert data; `none` for a plan it cannot run. -/
private def interpret (plan : Plan) (input : Nat) : Option Result :=
  match (plan.steps.forM (runStep plan.helpers)).run {input} with
  | .ok ((), machine) => some (.returned machine.acc)
  | .error (.revert data) => some (.reverted data)
  | .error (.fault _) => none

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 200 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  let mut reverted := 0
  let mut lengths : List Nat := []
  for seed in List.range 200 do
    match RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
          if let .reverted data := core then
            reverted := reverted + 1
            unless lengths.contains data.length do lengths := data.length :: lengths
  ensure (compared = 2400) "fewer than 200 generated plans compared with the interpreter"
  ensure (reverted ≥ 600 && compared - reverted ≥ 600) "fewer than 600 compared outcomes reverted or returned"
  for length in [0, 1, 4, 31, 32, 33, 63, 64] do
    ensure (lengths.contains length) s!"no compared outcome reverted with {length} bytes"

/-! Two fixtures. The first makes a selector through a helper and a message of
a 64-byte value, reverts with a literal, writes a byte of the message's value,
passes the message through a function value to a helper calling a `require`
helper, takes a sum holding the selector, applies a closure with a 63-byte
`require` literal, raises a message of a value a bounded loop allocates, and
reads the written value. The second makes a message of a 5-byte value through
a helper, picks it or `Error.Empty` by the input, writes through a second
variable of the value, takes a pair holding the picked `Error`, calls a helper
raising its own selector, takes an enum holding the message, then reverts
empty on the accumulator and with a 64-byte `require` literal. -/

private def fixtureA : Plan := {
  helpers := [
    .raise {form := .require, cond := {word := .input, test := .lt 1000}, payload := .error .param} .add 3,
    .make 7,
    .call 0 9],
  steps := [
    .action (.bytes (.concat (.word .input) (.word (.mul 3)))),
    .error (.helper 1 (.xor 9)),
    .error (.make (.message 0)),
    .site {form := .when, cond := {word := .input, test := .bits 3 2}, payload := .literal 3},
    .action (.write (.bytes 0) (.literal 31) (.add 1) .byte .inline),
    .call 2 (.named 1) (.add 5) false .xor 5,
    .data (.inl (.named 0)),
    .take (.sum 0) {form := .when, cond := {word := .input, test := .gt 255}, payload := .error .param} .add 7,
    .closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .literal 8} .add 3,
    .apply 0 .input .xor 9,
    .loop 3 [.action (.bytes (.toBytes (.word .counter))),
      .site {form := .when, cond := {word := .counter, test := .eq 2}, payload := .error (.make (.message 1))}],
    .action (.observe .add 3 (.bytes 0) (.word (.literal 0)))]}

private def fixtureB : Plan := {
  helpers := [
    .message,
    .pick (.bits 1 1),
    .raise {form := .when, cond := {word := .xor 255, test := .eq 0}, payload := .error (.make (.selector (.add 2)))}
      .xor 7],
  steps := [
    .action (.bytes (.toBytes (.zeros 5))),
    .action (.alias (.bytes 0)),
    .error (.message 0 0),
    .error (.pick 1 .input (.named 0) (.make .empty)),
    .action (.write (.bytes 1) (.literal 4) .input .byte .helper),
    .data (.pair (.named 1) (.add 1)),
    .take (.pair 0) {form := .require, cond := {word := .input, test := .ne 256}, payload := .error .param} .add 5,
    .call 2 (.make .empty) .input true .add 3,
    .data (.first (.named 0) (.mul 3)),
    .take (.enum 0) {form := .when, cond := {word := .input, test := .eq 2}, payload := .error .param} .xor 11,
    .site {form := .when, cond := {word := .acc, test := .bits 7 5}, payload := .none},
    .site {form := .require, cond := {word := .input, test := .lt (2 ^ 255)}, payload := .literal 9}]}

/-- From the Python model of `Tests/scripts/test-semantic-revert-data-corpus.py`:
a returned Word in decimal, revert data in hex. -/
private def fixtureAResults : List (Nat × String) := [
  (0, "463"),
  (1, "0x74686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672030313233343536373839206162636465666768"),
  (2, "0x746f6f206c61726765"),
  (255, "0x0000000000000000000000000000000000000000000000000000000000000002"),
  (256, "0x00000110"),
  (2 ^ 256 - 1, "0xfffffffd"),
  (2 ^ 255, "0x80000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000"),
  (2 ^ 255 - 1, "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd"),
  (3, "0x0000000000000000000000000000000000000000000000000000000000000002"),
  (5, "624"),
  (6, "0x746f6f206c61726765"),
  (1001, "0x00000000000000000000000000000000000000000000000000000000000003ea0000000000000000000000000000000000000000000000000000000000000bbb")]

private def fixtureBResults : List (Nat × String) := [
  (0, "110"),
  (1, "135"),
  (2, "0x0000000002"),
  (255, "0x00000101"),
  (256, "0x"),
  (2 ^ 256 - 1, "0x"),
  (2 ^ 255, "0x74686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67203031323334353637383920616263646566676869"),
  (2 ^ 255 - 1, "0x"),
  (3, "185"),
  (5, "211"),
  (6, "224"),
  (1001, "42975")]

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
  "function sc_h0(sc_e: Error, sc_w: word) returns (word) {",
  "    require((sc_w < 1000), sc_e);",
  "    return (sc_w + 3);",
  "}",
  "",
  "function sc_h1(sc_w: word) returns (Error) {",
  "    return Error((sc_w + 7));",
  "}",
  "",
  "function sc_h2(sc_e: Error, sc_w: word) returns (word) {",
  "    return sc_h0(sc_e, (sc_w + 9));",
  "}",
  "",
  "contract SynthesizedRevertData {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = concat(bytes32(sc_x), bytes32((sc_x * 3)));",
  "        let sc_e0: Error = sc_h1((sc_x ^ 9));",
  "        let sc_e1: Error = Error.Msg(memory(Typedef.rep(sc_b0)));",
  "        if ((sc_x & 3) == 2) {",
  "            revertLit(\"too large\");",
  "        }",
  "        mstore8(MemoryPointer.ptr(truncate(slice_(sc_b0, 31), 1)), (sc_x + 1));",
  "        let sc_f0: function (Error, word) returns (word) = sc_h2;",
  "        sc_r = ((sc_r * 5) ^ sc_f0(sc_e1, (sc_x + 5)));",
  "        let sc_u0: sum<Error, word> = inl(sc_e0);",
  "        match (sc_u0) {",
  "            case inl(sc_e) {",
  "                if (sc_x > 255) {",
  "                    revertWithError(sc_e);",
  "                }",
  "            }",
  "            case inr(sc_w) {",
  "                sc_r = ((sc_r * 7) + sc_w);",
  "            }",
  "        }",
  "        let sc_c0: function (word) returns (word) = lam (sc_j: word) -> word {",
  "            require((sc_j != 1), \"the quick brown fox jumps over the lazy dog 0123456789 abcdefgh\");",
  "            return (sc_j + 3);",
  "        };",
  "        sc_r = ((sc_r * 9) ^ sc_c0(sc_x));",
  "        let sc_limit: word = (sc_x & 3);",
  "        let sc_counter: word = 0;",
  "        while (sc_limit > sc_counter) {",
  "            let sc_b1: memory<bytes> = to_bytes(bytes32(sc_counter));",
  "            if (sc_counter == 2) {",
  "                revertWithError(Error.Msg(memory(Typedef.rep(sc_b1))));",
  "            }",
  "            sc_counter = (sc_counter + 1);",
  "        }",
  "        sc_r = ((sc_r * 3) + sc_word(sc_b0, 0));",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureBSource : String := String.intercalate "\n" (header ++ [
  "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
  "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);",
  "}",
  "",
  "enum Sc_F {",
  "    Sc_F0(Error, word),",
  "    Sc_F1(word)",
  "}",
  "",
  "function sc_h0(sc_v: memory<bytes>) returns (Error) {",
  "    return Error.Msg(memory(Typedef.rep(sc_v)));",
  "}",
  "",
  "function sc_h1(sc_w: word, sc_a: Error, sc_b: Error) returns (Error) {",
  "    if ((sc_w & 1) == 1) {",
  "        return sc_a;",
  "    }",
  "    return sc_b;",
  "}",
  "",
  "function sc_h2(sc_e: Error, sc_w: word) returns (word) {",
  "    if ((sc_w ^ 255) == 0) {",
  "        revertWithError(Error((sc_w + 2)));",
  "    }",
  "    return (sc_w ^ 7);",
  "}",
  "",
  "contract SynthesizedRevertData {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = to_bytes(empty(5));",
  "        let sc_b1: memory<bytes> = sc_b0;",
  "        let sc_e0: Error = sc_h0(sc_b0);",
  "        let sc_e1: Error = sc_h1(sc_x, sc_e0, Error.Empty);",
  "        sc_put8(sc_b1, 4, sc_x);",
  "        let sc_t0: (Error, word) = (sc_e1, (sc_x + 1));",
  "        match (sc_t0) {",
  "            case (sc_e, sc_w) {",
  "                require((sc_x != 256), sc_e);",
  "                sc_r = ((sc_r * 5) + sc_w);",
  "            }",
  "        }",
  "        sc_r = ((sc_r * 3) + sc_h2(Error.Empty, sc_x));",
  "        let sc_g0: Sc_F = Sc_F.Sc_F0(sc_e0, (sc_x * 3));",
  "        match (sc_g0) {",
  "            case Sc_F.Sc_F0(sc_e, sc_w) {",
  "                if (sc_x == 2) {",
  "                    revertWithError(sc_e);",
  "                }",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "            case Sc_F.Sc_F1(sc_w) {",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "        }",
  "        if ((sc_r & 7) == 5) {",
  "            revertEmpty();",
  "        }",
  "        require((sc_x < 57896044618658097711785492504343953926634992332820282019728792003956564819968), " ++
    "\"the quick brown fox jumps over the lazy dog 0123456789 abcdefghi\");",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureAShapes : List (String × List String) := [
  ("helpers", ["call", "make", "raise"]),
  ("forms", ["require", "requireLiteral", "revertLit", "revertWithError"]),
  ("errors", ["message", "selector"]),
  ("contexts", ["call", "closure", "loop", "run", "sum"]),
  ("carriers", ["held", "loop", "value"]),
  ("declarations", ["made", "variable"]),
  ("data", ["inl"]),
  ("tests", ["bits", "eq", "gt", "lt", "ne"]),
  ("words", ["counter", "input", "local"]),
  ("lengths", ["1-31", "32", "33-63", "64"]),
  ("hazards", ["written"]),
  ("steps", ["action", "apply", "call", "closure", "data", "error", "loop", "site", "take"])]

private def fixtureBShapes : List (String × List String) := [
  ("helpers", ["message", "pick", "raise"]),
  ("forms", ["require", "requireLiteral", "revertEmpty", "revertWithError"]),
  ("errors", ["message", "picked", "selector"]),
  ("contexts", ["enum", "helper", "pair", "run"]),
  ("carriers", ["held", "inline"]),
  ("declarations", ["messaged", "picked"]),
  ("data", ["enum0", "pair"]),
  ("tests", ["bits", "eq", "lt", "ne"]),
  ("words", ["acc", "input", "local"]),
  ("lengths", ["0", "1-31", "64"]),
  ("hazards", ["alias", "written"]),
  ("steps", ["action", "call", "data", "error", "site", "take"])]

private def fixtureChecks : IO Unit := do
  for (label, plan, source, results, shapes) in [
      ("first", fixtureA, fixtureASource, fixtureAResults, fixtureAShapes),
      ("second", fixtureB, fixtureBSource, fixtureBResults, fixtureBShapes)] do
    ensure plan.admitted s!"the {label} fixture plan is not admitted"
    let some checked := RevertData.CheckedPlan.ofPlan? plan
      | throw (IO.userError s!"the {label} fixture failed the checker")
    ensure ((RevertData.emit plan).source == source) s!"the {label} fixture source changed"
    for (value, expected) in results do
      ensure ((← run (checked.program (Word.ofNatModulo value))).text == expected) s!"{label} fixture input {value}: Core result"
      ensure ((interpret plan value).map Result.text == some expected) s!"{label} fixture input {value}: interpreter result"
    ensure (plan.shapes == shapes) s!"the {label} fixture shapes changed"
    ensure (match RevertData.planOf (RevertData.planJson plan) with
      | .ok decoded => decoded == plan
      | .error _ => false) s!"the {label} fixture plan JSON does not round-trip"
  let some first := RevertData.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  let some second := RevertData.CheckedPlan.ofPlan? fixtureB
    | throw (IO.userError "the second fixture failed the checker")
  ensure (RevertData.observe first (Word.ofNatModulo 256) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0x00000110")])
    "a selector's low four bytes are not observed as the revert data"
  ensure (RevertData.observe second (Word.ofNatModulo 256) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0x")])
    "an empty revert is not observed as empty revert data"

private def withStep (plan : Plan) (index : Nat) (replacement : Step) : Plan :=
  {plan with steps := plan.steps.set index replacement}

private def withHelper (plan : Plan) (index : Nat) (replacement : Helper) : Plan :=
  {plan with helpers := plan.helpers.set index replacement}

/-- Admission refuses what the compiler, the lowerings or the reference
cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let admitted := fun (label : String) (plan : Plan) => ensure plan.admitted s!"refused {label}"
  let a := fixtureA
  let b := fixtureB
  let bytes := Step.action (.bytes (.concat (.word .input) (.word .input)))
  let observe := Step.action (.observe .add 3 (.bytes 0) .length)
  let quiet : Site := {form := .when, cond := {word := .input, test := .eq 0}, payload := .none}
  let plain := fun (steps : List Step) => ({helpers := [], steps} : Plan)
  let raising := fun (steps : List Step) => ({helpers := [.raise quiet .add 3], steps} : Plan)
  let call := Step.call 0 (.make .empty) .input false .add 3
  let siteA := fun (payload : Payload) => withStep a 3 (.site {form := .when, cond := {word := .input, test := .bits 3 2}, payload})
  let testA := fun (test : Test) =>
    withStep a 7 (.take (.sum 0) {form := .when, cond := {word := .input, test}, payload := .error .param} .add 7)
  let helperB := fun (word : Operand) (payload : Payload) =>
    withHelper b 2 (.raise {form := .when, cond := {word, test := .eq 0}, payload} .xor 7)
  let loop := fun (mask : Nat) (body : List Item) => plain [bytes, .loop mask body, observe]
  admitted "a site and an observation" (plain [bytes, .site quiet, observe])
  refused "four helpers" ({a with helpers := a.helpers ++ [.message]} : Plan)
  refused "no step" ({a with steps := []} : Plan)
  refused "thirteen steps" ({a with steps := a.steps ++ [observe]} : Plan)
  refused "no site" (plain [bytes, observe])
  refused "no fold" (plain [.site quiet])
  refused "a helper calling itself" (withHelper a 2 (.call 2 9))
  refused "a helper calling a later one" (withHelper a 0 (.call 2 9))
  refused "a call of a make helper" (withHelper a 2 (.call 1 9))
  refused "a call constant of 0" (withHelper a 2 (.call 0 0))
  refused "a call constant of 256" (withHelper a 2 (.call 0 256))
  refused "a make constant of 0" (withHelper a 1 (.make 0))
  refused "a make constant of 256" (withHelper a 1 (.make 256))
  refused "an even fold constant" (withHelper a 0
    (.raise {form := .require, cond := {word := .input, test := .lt 1000}, payload := .error .param} .add 4))
  refused "the accumulator in a helper" (helperB .acc (.error (.make (.selector (.add 2)))))
  refused "a selector of the accumulator in a helper" (helperB (.xor 255) (.error (.make (.selector .acc))))
  refused "a message in a helper" (helperB (.xor 255) (.error (.make (.message 0))))
  refused "a named Error in a helper" (helperB (.xor 255) (.error (.named 0)))
  refused "an Error parameter in run" (siteA (.error .param))
  refused "an Error parameter in a closure" (withStep a 8
    (.closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .error .param} .add 3))
  refused "the accumulator in a closure" (withStep a 8
    (.closure {form := .require, cond := {word := .acc, test := .ne 1}, payload := .literal 8} .add 3))
  refused "a 33-byte revertLit" (siteA (.literal 7))
  admitted "a 32-byte revertLit" (siteA (.literal 6))
  refused "a literal past the table" (withStep a 8
    (.closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .literal 10} .add 3))
  refused "revertEmpty through require" (withStep b 10
    (.site {form := .require, cond := {word := .acc, test := .bits 7 5}, payload := .none}))
  refused "an order constant of 4" (testA (.gt 4))
  refused "an equality constant of 4" (testA (.eq 4))
  refused "a bit value above its mask" (testA (.bits 1 2))
  refused "a bit mask of 4" (testA (.bits 4 0))
  refused "a counter outside a loop" (withStep b 10
    (.site {form := .when, cond := {word := .counter, test := .bits 7 5}, payload := .none}))
  refused "a selector of a counter outside a loop" (withStep a 1 (.error (.helper 1 .counter)))
  let message := fun (value : Nat) => Step.site {quiet with payload := .error (.make (.message value))}
  refused "a message past 64 bytes" (plain [bytes, .action (.bytes (.concat (.value (.bytes 0)) (.zeros 1))), message 1, observe])
  admitted "a 64-byte message" (plain [bytes, .action (.bytes (.concat (.value (.bytes 0)) (.zeros 1))), message 0, observe])
  refused "a message of an undeclared value" (withStep a 2 (.error (.make (.message 3))))
  refused "a fourth Error variable" (plain ([bytes] ++ List.replicate 4 (.error (.make .empty)) ++ [.site quiet, observe]))
  admitted "three Error variables" (plain ([bytes] ++ List.replicate 3 (.error (.make .empty)) ++ [.site quiet, observe]))
  refused "a third pair" (plain ([bytes] ++ List.replicate 3 (.data (.pair (.make .empty) .input)) ++ [.site quiet, observe]))
  refused "a third sum" (plain ([bytes] ++ List.replicate 3 (.data (.inr .input)) ++ [.site quiet, observe]))
  refused "a third enum" (plain ([bytes] ++ List.replicate 3 (.data (.second .input)) ++ [.site quiet, observe]))
  admitted "two of each data value" (plain ([bytes] ++ List.replicate 2 (.data (.pair (.make .empty) .input)) ++
    List.replicate 2 (.data (.inr .input)) ++ List.replicate 2 (.data (.second .input)) ++ [.site quiet, observe]))
  refused "a third closure" (plain ([bytes] ++ List.replicate 3 (.closure quiet .add 3) ++ [.site quiet, observe]))
  refused "a third function value" (raising (List.replicate 3 call))
  admitted "two function values" (raising (List.replicate 2 call))
  refused "two loops" (plain [bytes, .loop 1 [.site quiet], .loop 1 [.site quiet], observe])
  admitted "a loop" (loop 1 [.site quiet])
  refused "a loop mask of 2" (loop 2 [.site quiet])
  refused "an empty loop" (loop 1 [])
  refused "a loop of four items" (loop 1 (List.replicate 4 (.site quiet)))
  refused "a loop that writes" (loop 1 [.action (.write (.bytes 0) (.literal 0) .input .byte .inline), .site quiet])
  refused "a loop that observes" (loop 1 [.action (.observe .add 3 (.bytes 0) .length), .site quiet])
  refused "a loop that names a value twice" (loop 1 [.action (.alias (.bytes 0)), .site quiet])
  refused "a slice" (plain [bytes, .action (.slice (.bytes 0) (.drop 0)), .site quiet, observe])
  refused "an array" (plain [bytes, .action (.array false [.input]), .site quiet, observe])
  refused "a hash" (plain [bytes, .site quiet, .action (.observe .add 3 (.bytes 0) .hash)])
  refused "an input position" (plain [bytes, .site quiet, .action (.observe .add 3 (.bytes 0) (.word (.input 0 32)))])
  refused "an application of a missing closure" (withStep a 9 (.apply 1 .input .xor 9))
  refused "a take of a missing sum" (withStep a 7
    (.take (.sum 1) {form := .when, cond := {word := .input, test := .gt 255}, payload := .error .param} .add 7))
  refused "a selector from a raise helper" (withStep a 1 (.error (.helper 0 (.xor 9))))
  refused "a message from a pick helper" (withStep b 2 (.error (.message 1 0)))
  refused "a pick of a missing Error" (withStep b 3 (.error (.pick 1 .input (.named 1) (.make .empty))))
  refused "a call of a pick helper" (withStep b 7 (.call 1 (.make .empty) .input true .add 3))
  refused "a call of a missing helper" (withStep b 7 (.call 3 (.make .empty) .input true .add 3))
  refused "a counter in a call" (withStep b 7 (.call 2 (.make .empty) .counter true .add 3))
  refused "an even call fold constant" (withStep b 7 (.call 2 (.make .empty) .input true .add 4))

private def shapeValues : List (String × List String) := [
  ("helpers", ["call", "make", "message", "pick", "raise"]),
  ("forms", ["require", "requireLiteral", "revertEmpty", "revertLit", "revertWithError"]),
  ("errors", ["empty", "message", "picked", "selector"]),
  ("contexts", ["call", "closure", "enum", "helper", "loop", "pair", "run", "sum"]),
  ("carriers", ["captured", "held", "inline", "loop", "passed", "value", "variable"]),
  ("declarations", ["made", "messaged", "picked", "variable"]),
  ("data", ["enum0", "enum1", "inl", "inr", "pair"]),
  ("tests", ["bits", "eq", "gt", "lt", "ne"]),
  ("words", ["acc", "constant", "counter", "input", "local"]),
  ("lengths", ["0", "1-31", "32", "33-63", "64"]),
  ("hazards", ["alias", "allocated", "written"]),
  ("steps", ["action", "apply", "call", "closure", "data", "error", "loop", "site", "take"])]

/-- Generation is deterministic, its accepted plans draw every shape within
1,000 seeds, it replays exactly and drops steps to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 1000 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (RevertData.planJson plan == RevertData.planJson (generate (UInt64.ofNat (seed + 1))))
      "generation is not deterministic"
    if let .ok checked := RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes then
      if (RevertData.inputSensitive checked fuel).isOk then
        for (dimension, values) in checked.plan.shapes do
          for value in values do
            ensure ((shapeValues.lookup dimension).any (·.contains value)) s!"unknown shape {dimension}:{value}"
            unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"1,000 seeds never drew {dimension}:{value}"
  let all ← cases (RevertData.generateCases (Seed.ofNat 1) RevertData.defaultNodes 64 64 fuel)
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  let mut reverted := 0
  for case in all do
    ensure ((← expect (RevertData.replayCase case fuel)) == case) "a generated case failed exact replay"
    let direct ← expect (case.getObjVal? "directCore")
    if (direct.getObjValAs? String "status").toOption == some "reverted" then reverted := reverted + 1
  ensure (reverted ≥ 16 && reverted ≤ 48) "fewer than a quarter of 64 generated cases reverted or returned"
  let seeded ← cases (RevertData.generateCases (Seed.ofNat 7) RevertData.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← expect (RevertData.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 200 do
    if let .ok small := RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.minimumNodes then
      ensure (small.plan.nodes ≤ RevertData.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.steps.length < (generate (UInt64.ofNat (seed + 1))).steps.length then dropped := true
  ensure dropped "a 256-node budget never dropped a step"

/-- Which part of a site a reduction changed. -/
private def siteKind (before after : Site) : String :=
  if before.form != after.form then "require"
  else if before.payload != after.payload then "payload"
  else if before.cond.test != after.cond.test then "test"
  else "word"

/-- What a reduction changed, from the first helper or step that differs. -/
private def reductionKind (previous next : Plan) (inputChanged : Bool) : String :=
  if inputChanged then "input"
  else if next.helpers.length < previous.helpers.length then "helper"
  else if next.helpers != previous.helpers then
    match (previous.helpers.zip next.helpers).find? (fun (before, after) => before != after) with
    | some (.raise single fold constant, .raise single' fold' constant') =>
        if single != single' then siteKind single single' else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.pick test, .pick test') => if test != test' then "test" else "none"
    | some (.make _, .make _) | some (.call .., .call ..) => "constant"
    | _ => "none"
  else if next.steps.length < previous.steps.length then "step"
  else match (previous.steps.zip next.steps).find? (fun (before, after) => before != after) with
    | some (.call .., .site _) => "inline"
    | some (.call _ error word direct fold constant, .call _ error' word' direct' fold' constant') =>
        if direct != direct' then "form" else if error != error' then "argument"
        else if word != word' then "word" else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.error _, .error _) => "decl"
    | some (.data _, .data _) => "data"
    | some (.site single, .site single') => siteKind single single'
    | some (.take _ single fold constant, .take _ single' fold' constant')
    | some (.closure single fold constant, .closure single' fold' constant') =>
        if single != single' then siteKind single single' else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.apply _ word fold constant, .apply _ word' fold' constant') =>
        if word != word' then "word" else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.loop mask body, .loop mask' body') =>
        if mask != mask' then "mask" else if body.length != body'.length then "body"
        else match (body.zip body').find? (fun (before, after) => before != after) with
          | some (.site single, .site single') => siteKind single single'
          | _ => "none"
    | _ => "none"

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, every kind applies, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (RevertData.generateCases (Seed.ofNat 1) RevertData.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← expect (case.getObjVal? "revertDataPlan")
  ensure (RevertData.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (RevertData.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-revert-data-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "revertDataShapes" (Json.mkObj []))) fuel matches .error _) "changed revert data shapes replayed"
  ensure (RevertData.replayCase (case.setObjVal! "revertDataPlan" (plan.setObjVal! "steps" (.arr #[]))) fuel
    matches .error _) "a plan without steps replayed"
  ensure (RevertData.replayCase (case.setObjVal! "schema" (toJson "solcore-lean.semantic-revert-data-case.v0")) fuel
    matches .error _) "a changed case schema replayed"
  ensure (RevertData.replayCase (case.setObjVal! "directCore" (Json.mkObj [("stage", toJson "execution"),
      ("status", toJson "reverted"), ("output", toJson "0x00")])) fuel matches .ok _)
    "replay read the saved observation"
  let origin ← expect ((← provenance case).getObjVal? "origin")
  ensure (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let fixture := RevertData.planJson fixtureA
  let some fixtureChecked := RevertData.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  let fixtureCase := RevertData.makeCase fixtureChecked (Word.ofNatModulo 5)
    (RevertData.emit fixtureA) (Json.mkObj [("kind", toJson "imported")]) fuel
  ensure ((← expect (RevertData.replayCase fixtureCase fuel)) == fixtureCase) "the imported fixture case failed replay"
  let helpers ← expect (fixture.getObjValAs? (Array Json) "helpers")
  let changed := helpers.set! 2 (RevertData.helperJson (.call 0 8))
  ensure (RevertData.replayCase (fixtureCase.setObjVal! "revertDataPlan" (fixture.setObjVal! "helpers" (.arr changed))) fuel
    matches .error _) "a changed helper replayed against the saved reference"
  let shrunk ← expect (RevertData.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← expect (RevertData.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← expect (RevertData.caseProgram case)
  for reduction in RevertData.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  let sources := [fixtureA, fixtureB].filterMap RevertData.CheckedPlan.ofPlan? ++ (List.range 40).filterMap fun seed =>
    (RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes).toOption
  for checked in sources do
    let source : RevertData.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
    for reduction in RevertData.reductions source do
      let kind := reductionKind checked.plan reduction.candidate.plan.plan (reduction.candidate.input != source.input)
      unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["step", "helper", "inline", "form", "argument", "word", "fold", "decl", "data", "payload", "require",
      "test", "constant", "mask", "body", "input"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in the fixtures and 40 plans"
  let reducedOrigin ← expect ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (RevertData.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← expect (reduced[0]!.getObjVal? "revertDataPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceRevertDataCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceRevertDataCases
