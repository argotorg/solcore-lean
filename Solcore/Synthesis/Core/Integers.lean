import Solcore.Synthesis.Core.EnumData

/-! std's integer types and their operators in pure functions, the plans of
the `runtime-checked-arithmetic` and `runtime-shifts` profiles: `uint8` …
`uint256` and `int8` … `int256` converted from the input Word, checked
`+ - * / %` and unary `-` with std's `Panic(0x11)` and `Panic(0x12)`, the same
operations inside `unchecked { … }` blocks, through helpers and lambda bodies
whose own scope decides, compound assignments, typed literals at the types'
extremes, `uint256` literals typed only by defaulting, a `run(T)` argument
that std's ABI decoder validates, a `T` result that std's encoder masks or
sign-extends; and `<<`, `>>`, `<<=` and `>>=` of Words and integers by amounts
of every unsigned type.

The original Core reference reads each representation Word as an integer and
computes the exact result, which a checked operation range-checks against its
type and an unchecked one wraps to the type's width; a quotient rounds toward
zero, from the floor quotient of the magnitudes. It returns the left injection
of the Words folded by the source, or the right injection of the revert data:
its length and its bytes in two Words, the `runtime-revert-data` encoding. The
input conversions and the fold are the source's own Word operations. Nothing
here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Integers

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)

def integerVersion : String := "core-integers-v1"

/-! Types. -/

/-- `uint8` … `uint256` or `int8` … `int256`, of 1, 2, 4, 8, 16 or 32 bytes. -/
structure IntType where
  signed : Bool
  bytes : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

namespace IntType

def widths : List Nat := [1, 2, 4, 8, 16, 32]

/-- The unsigned types, then the signed ones, narrowest first. -/
def all : List IntType :=
  (widths.map fun bytes => ({signed := false, bytes} : IntType)) ++
    widths.map fun bytes => ({signed := true, bytes} : IntType)

def bits (type : IntType) : Nat := 8 * type.bytes

def name (type : IntType) : String := (if type.signed then "int" else "uint") ++ toString type.bits

def admitted (type : IntType) : Bool := widths.contains type.bytes

def minimum (type : IntType) : Int := if type.signed then -((2 : Int) ^ (type.bits - 1)) else 0

def maximum (type : IntType) : Int :=
  if type.signed then (2 : Int) ^ (type.bits - 1) - 1 else (2 : Int) ^ type.bits - 1

def inRange (type : IntType) (value : Int) : Bool :=
  decide (type.minimum ≤ value) && decide (value ≤ type.maximum)

/-- The value wrapped to the type's width, two's complement for a signed type. -/
def wrap (type : IntType) (value : Int) : Int :=
  (value - type.minimum) % (2 : Int) ^ type.bits + type.minimum

/-- The representation Word of a value: its residue modulo `2^256`. -/
def rep (value : Int) : Nat := (value % (2 : Int) ^ 256).toNat

/-- The value a representation Word holds. -/
def value (type : IntType) (word : Nat) : Int :=
  if type.signed && decide (2 ^ 255 ≤ word) then (word : Int) - (2 : Int) ^ 256 else word

/-- A Word converted as the source converts it: its low bits, sign-extended
for a signed type. -/
def convert (type : IntType) (word : Nat) : Nat :=
  if type.bytes = 32 then word % 2 ^ 256
  else if type.signed then rep (type.wrap (word % 2 ^ type.bits : Nat))
  else word % 2 ^ type.bits

/-- Whether std's ABI decoder admits the Word as an argument of the type. -/
def canonical (type : IntType) (word : Nat) : Bool := type.convert word == word

/-- The typed literals: the extremes and their neighbours, `-1` for a signed
type, 0 to 3, 7 and two to half the width. -/
def literals (type : IntType) : List Int :=
  (if type.signed then [type.minimum, type.minimum + 1, -1] else []) ++
    [0, 1, 2, 3, 7, (2 : Int) ^ (type.bits / 2), type.maximum - 1, type.maximum]

def literalClass (type : IntType) (index : Nat) : String :=
  ((if type.signed then ["min", "min1", "minus1"] else []) ++
    ["zero", "one", "small", "small", "small", "half", "max1", "max"]).getD index "none"

/-- Offsets added to the input Word before it is converted, so that the eight
boundary inputs reach each type's extremes. -/
def offsets (type : IntType) : List Nat :=
  [0, 1, 3, 2 ^ (type.bits - 1) - 1, 2 ^ (type.bits - 1), 2 ^ type.bits - 1]

/-- The selector of `run(T)`, `keccak256` of the signature. -/
def selector (type : IntType) : String :=
  match type.signed, type.bytes with
  | false, 1 => "0xc4e5557a" | false, 2 => "0x1f63069c" | false, 4 => "0x0f6d710c"
  | false, 8 => "0x8a52d919" | false, 16 => "0xedc3b5ad" | false, _ => "0xa444f5e9"
  | true, 1 => "0x1778c9c6" | true, 2 => "0x091ebc26" | true, 4 => "0x23040ce1"
  | true, 8 => "0xec784157" | true, 16 => "0x96c07422" | true, _ => "0x61a47706"

def uint256 : IntType := {signed := false, bytes := 32}

end IntType

/-- A shifted value's type, or an amount's: a Word or an integer type. A Word
behaves as `uint256` and is written as itself. -/
inductive ValueType where
  | word
  | int (type : IntType)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace ValueType

def type : ValueType → IntType
  | .word => IntType.uint256
  | .int type => type

def name : ValueType → String
  | .word => "word"
  | .int type => type.name

def admitted : ValueType → Bool
  | .word => true
  | .int type => type.admitted

/-- An amount is a Word or an unsigned integer. -/
def amountAdmitted : ValueType → Bool
  | .word => true
  | .int type => type.admitted && !type.signed

/-- The Word, then the integer types. -/
def all : List ValueType := .word :: IntType.all.map .int

/-- The Word and the unsigned integer types. -/
def amounts : List ValueType := .word :: (IntType.all.filter (!·.signed)).map .int

end ValueType

/-! Plans. -/

inductive Op where
  | add
  | sub
  | mul
  | div
  | mod
  deriving Repr, BEq, DecidableEq, Inhabited

def Op.all : List Op := [.add, .sub, .mul, .div, .mod]

def Op.name : Op → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"

/-- An operand of the plan's type: `sc_a<i>`, the input converted after its
offset, `sc_v<n>`, an earlier step's variable, or a typed literal. -/
inductive Operand where
  | input (index : Nat)
  | var (index : Nat)
  | literal (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A test of the input Word: `(sc_x < c)`, `(sc_x > c)`, `(sc_x == c)` or
`((sc_x & m) == k)`. -/
inductive Test where
  | lt (constant : Nat)
  | gt (constant : Nat)
  | eq (constant : Nat)
  | bits (mask value : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def testConstants : List Nat := [0, 1, 2, 7, 255, 256, 2 ^ 255]
def testMasks : List Nat := [1, 3, 7]

def Test.admitted : Test → Bool
  | .lt constant | .gt constant | .eq constant => testConstants.contains constant
  | .bits mask value => testMasks.contains mask && value ≤ mask

/-- How a step assigns its variable `sc_v<n>`:
- `binary`: `(L op R)`;
- `neg`: `(-L)`;
- `compound`: `sc_v<n> = L;` then `sc_v<n> op= R;`;
- `call`: `sc_h<k>(L, R)`, whose own scope decides;
- `apply`: `sc_apply(lam (sc_l: T) -> T { return (sc_l op R); }, L)`, its
  body checked unless `unchecked` puts it in a block. -/
inductive Form where
  | binary (op : Op) (left right : Operand)
  | neg (operand : Operand)
  | compound (op : Op) (left right : Operand)
  | call (helper : Nat) (left right : Operand)
  | apply (op : Op) (unchecked : Bool) (left right : Operand)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `uint256` literals typed only by defaulting: `let sc_d<m> = L;`,
`if (C) { sc_d<m> = L'; }`, then `sc_e<m>` is `(sc_d<m> op L'')`, the
literals being `uint256`'s. -/
structure Default where
  initial : Nat
  test : Test
  chosen : Nat
  op : Op
  operand : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A shift amount: `sc_k<j>`, the input converted after its offset to its
amount type, or a literal amount. -/
inductive Amount where
  | input (index : Nat)
  | literal (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def amountLiterals : List Nat := [0, 1, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 300]
def amountOffsets : List Nat := [0, 1, 3, 7, 8, 31, 64, 127, 128, 254, 255, 256, 300]

inductive Direction where
  | left
  | right
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sc_v<n>` is `(V << K)` or `(V >> K)`, or `V` then `sc_v<n> <<= K;` or
`>>=`. -/
structure Shift where
  direction : Direction
  compound : Bool
  value : Operand
  amount : Amount
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Step where
  | assign (form : Form)
  | default (value : Default)
  | shift (value : Shift)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Consecutive steps in one context: inside one `unchecked { … }` block, or
not. -/
structure Group where
  unchecked : Bool
  steps : List Step
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sc_h<k>(sc_p: T, sc_q: T) returns (T)`, `return (sc_p op sc_q);`, in a
block when `unchecked`. -/
structure Helper where
  op : Op
  unchecked : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An amount `sc_k<j>`: the input plus its offset, converted to its type. -/
structure AmountInput where
  type : ValueType
  offset : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A plan of either profile: the value type, `run(T)` instead of
`run(uint256)`, a `T` result instead of `uint256`, the offsets of the inputs
`sc_a<i>`, the amounts `sc_k<j>`, the helpers and the steps in their groups. -/
structure Plan where
  value : ValueType
  abi : Bool
  raw : Bool
  inputs : List Nat
  amounts : List AmountInput
  helpers : List Helper
  groups : List Group
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Plan

def type (plan : Plan) : IntType := plan.value.type

/-- Every step with its group's context. -/
def steps (plan : Plan) : List (Bool × Step) :=
  plan.groups.flatMap fun group => group.steps.map (group.unchecked, ·)

def stepCount (plan : Plan) : Nat := (plan.groups.map (·.steps.length)).foldl (· + ·) 0

end Plan

/-! Admission. -/

def Operand.admitted (type : IntType) (inputs vars : Nat) : Operand → Bool
  | .input index => index < inputs
  | .var index => index < vars
  | .literal index => index < type.literals.length

def Amount.admitted (amounts : Nat) : Amount → Bool
  | .input index => index < amounts
  | .literal index => index < amountLiterals.length

def Form.helperIndex? : Form → Option Nat
  | .call helper _ _ => some helper
  | _ => none

def Form.admitted (type : IntType) (helpers inputs vars : Nat) (unchecked : Bool) : Form → Bool
  | .binary _ left right | .compound _ left right =>
      left.admitted type inputs vars && right.admitted type inputs vars
  | .neg operand => operand.admitted type inputs vars && !(operand matches .literal _)
  | .call helper left right =>
      helper < helpers && left.admitted type inputs vars && right.admitted type inputs vars
  | .apply _ body left right =>
      !(unchecked && body) && left.admitted type inputs vars && right.admitted type inputs vars

def Default.admitted (value : Default) : Bool :=
  let count := IntType.uint256.literals.length
  value.initial < count && value.chosen < count && value.operand < count && value.test.admitted

/-- The groups are nonempty, their contexts alternate and at most three are
blocks. -/
def groupsAdmitted (groups : List Group) : Bool :=
  !groups.isEmpty && groups.all (!·.steps.isEmpty) &&
    (groups.zip groups.tail).all (fun (first, second) => first.unchecked != second.unchecked) &&
    (groups.filter (·.unchecked)).length ≤ 3

namespace Plan

/-- Each step's operands are in scope; the counts are the variables before it. -/
def stepsAdmitted (plan : Plan) (arithmetic : Bool) : Bool := Id.run do
  let type := plan.type
  let mut vars := 0
  let mut defaults := 0
  for (unchecked, step) in plan.steps do
    match step with
    | .assign form =>
        unless arithmetic && form.admitted type plan.helpers.length plan.inputs.length vars unchecked do
          return false
        vars := vars + 1
    | .default value =>
        unless arithmetic && value.admitted do return false
        defaults := defaults + 1
    | .shift value =>
        unless !arithmetic && value.value.admitted type plan.inputs.length vars &&
            value.amount.admitted plan.amounts.length do
          return false
        vars := vars + 1
  return vars ≥ 1 && defaults ≤ 2

def calledHelpers (plan : Plan) : List Nat :=
  plan.steps.filterMap fun (_, step) => match step with
    | .assign form => form.helperIndex?
    | _ => none

def common (plan : Plan) : Bool :=
  let type := plan.type
  plan.value.admitted && 1 ≤ plan.inputs.length && plan.inputs.length ≤ 3 && plan.inputs.head? == some 0 &&
    plan.inputs.all (type.offsets.contains ·) && groupsAdmitted plan.groups &&
    1 ≤ plan.stepCount && plan.stepCount ≤ 10

/-- A `runtime-checked-arithmetic` plan: an integer type, no amounts, at most
two helpers, each called, a `T` result only for a narrow type. -/
def arithmeticAdmitted (plan : Plan) : Bool :=
  (plan.value matches .int _) && plan.common && plan.amounts.isEmpty && plan.helpers.length ≤ 2 &&
    (!plan.raw || plan.type.bytes < 32) &&
    (List.range plan.helpers.length).all (plan.calledHelpers.contains ·) && plan.stepsAdmitted true

/-- A `runtime-shifts` plan: shifts only, one to three amounts of a Word or
an unsigned type, no helpers, `run(uint256)` returning `uint256`. -/
def shiftAdmitted (plan : Plan) : Bool :=
  plan.common && !plan.abi && !plan.raw && plan.helpers.isEmpty && 1 ≤ plan.amounts.length &&
    plan.amounts.length ≤ 3 &&
    plan.amounts.all (fun amount => amount.type.amountAdmitted && amountOffsets.contains amount.offset) &&
    plan.stepsAdmitted false

end Plan

/-! A direct interpreter over integers, independent of the Core reference:
the shapes it reaches and the tests' second oracle. -/

/-- A run's outcome: the returned Word, a `Panic(code)`, or std's ABI
decoder's `DirtyHigherBitsForInteger()`. -/
inductive Outcome where
  | word (value : Nat)
  | panic (code : Nat)
  | dirty
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a run did: an operation that completed, wrapping or not; the
operation that panicked; or a shift by an amount to a result. `typed` is false
for the defaulted `uint256` operations. -/
inductive Event where
  | operation (name : String) (unchecked typed wrapped : Bool)
  | panic (name : String) (unchecked typed : Bool) (code : Nat)
  | shift (name : String) (amount : Nat) (result : Int)
  deriving Repr, BEq, Inhabited

def exact (op : Op) (left right : Int) : Int :=
  match op with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .div => left.tdiv right
  | .mod => left.tmod right

/-- An operation's representation Word, or its panic code: a zero divisor
panics with `0x12` in either context; a checked result outside the type
panics with `0x11`, an unchecked one wraps. -/
def operate (type : IntType) (unchecked : Bool) (op : Op) (left right : Int) : Except Nat (Nat × Bool) :=
  if (op == .div || op == .mod) && right == 0 then .error 0x12
  else
    let result := exact op left right
    if type.inRange result then .ok (IntType.rep result, false)
    else if unchecked then .ok (IntType.rep (type.wrap result), true)
    else .error 0x11

def negate (type : IntType) (unchecked : Bool) (operand : Int) : Except Nat (Nat × Bool) :=
  if type.inRange (-operand) then .ok (IntType.rep (-operand), false)
  else if unchecked then .ok (IntType.rep (type.wrap (-operand)), true)
  else .error 0x11

/-- The floor quotient by `2^amount`. -/
def floorShift (value : Int) (amount : Nat) : Int :=
  if 0 ≤ value then value / (2 : Int) ^ amount else -((-value - 1) / (2 : Int) ^ amount) - 1

def shiftResult (type : IntType) (direction : Direction) (value : Int) (amount : Nat) : Int :=
  match direction with
  | .left => if type.bits ≤ amount then 0 else type.wrap (value * (2 : Int) ^ amount)
  | .right => if 256 ≤ amount then (if value < 0 then -1 else 0) else floorShift value amount

def Test.holds (word : Nat) : Test → Bool
  | .lt constant => word < constant
  | .gt constant => word > constant
  | .eq constant => word == constant
  | .bits mask value => word % 2 ^ 256 &&& mask == value

def foldConstant : Nat := 1099511628211

def foldWord (acc value : Nat) : Nat := (acc * foldConstant % 2 ^ 256) ^^^ value

def Direction.name (type : ValueType) : Direction → String
  | .left => "shl"
  | .right => if type.type.signed then "sar" else "shr"

private structure Run where
  vars : List Nat := []
  results : List Nat := []
  events : List Event := []

namespace Plan

def amountWord (plan : Plan) (input : Nat) : Amount → Nat
  | .input index => match plan.amounts[index]? with
      | some amount => amount.type.type.convert ((input + amount.offset) % 2 ^ 256)
      | none => 0
  | .literal index => amountLiterals.getD index 0

/-- The outcome and events of a run at the input Word. -/
def run (plan : Plan) (input : Nat) : Outcome × List Event := Id.run do
  let type := plan.type
  let input := input % 2 ^ 256
  if plan.abi && !type.canonical input then return (.dirty, [])
  let inputs := plan.inputs.map fun offset => type.convert ((input + offset) % 2 ^ 256)
  let mut state : Run := {}
  for (unchecked, step) in plan.steps do
    let word (operand : Operand) : Nat := match operand with
      | .input index => inputs.getD index 0
      | .var index => state.vars.getD index 0
      | .literal index => IntType.rep (type.literals.getD index 0)
    let value (operand : Operand) : Int := type.value (word operand)
    let complete (result : Except Nat (Nat × Bool)) (name : String) (context typed : Bool) :
        Except (List Event) (Nat × Event) :=
      match result with
      | .ok (rep, wrapped) => .ok (rep, .operation name context typed wrapped)
      | .error code => .error (state.events ++ [.panic name context typed code])
    let outcome : Except (List Event) (Nat × Event × Bool) := match step with
      | .assign form => match form with
          | .binary op left right | .compound op left right =>
              (complete (operate type unchecked op (value left) (value right)) op.name unchecked true).map
                fun (rep, event) => (rep, event, true)
          | .neg operand =>
              (complete (negate type unchecked (value operand)) "neg" unchecked true).map
                fun (rep, event) => (rep, event, true)
          | .call helper left right =>
              let helper := plan.helpers.getD helper default
              (complete (operate type helper.unchecked helper.op (value left) (value right)) helper.op.name
                helper.unchecked true).map fun (rep, event) => (rep, event, true)
          | .apply op body left right =>
              (complete (operate type body op (value left) (value right)) op.name body true).map
                fun (rep, event) => (rep, event, true)
      | .default made =>
          let literal (index : Nat) : Int := IntType.uint256.literals.getD index 0
          let chosen := if made.test.holds input then literal made.chosen else literal made.initial
          (complete (operate IntType.uint256 unchecked made.op chosen (literal made.operand)) made.op.name
            unchecked false).map fun (rep, event) => (rep, event, false)
      | .shift shift =>
          let amount := plan.amountWord input shift.amount
          let result := shiftResult type shift.direction (value shift.value) amount
          .ok (IntType.rep result, .shift (shift.direction.name plan.value) amount result, true)
    match outcome with
    | .error events =>
        return (.panic (match events.getLast? with
          | some (.panic _ _ _ code) => code
          | _ => 0), events)
    | .ok (rep, event, isVar) =>
        let vars := if isVar then state.vars ++ [rep] else state.vars
        state := {vars, results := state.results ++ [rep], events := state.events ++ [event]}
  let acc := state.results.foldl foldWord 0
  return (.word (if plan.raw then type.convert acc else acc), state.events)

def outcome (plan : Plan) (input : Nat) : Outcome := (plan.run input).1

end Plan

/-! The reference compiler. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def int (value : Int) : Expr := .integer value
private def ilt (left right : Expr) : Expr := .binary .integerLt left right
private def isub (left right : Expr) : Expr := .binary .integerSub left right
private def iadd (left right : Expr) : Expr := .binary .integerAdd left right
private def imul (left right : Expr) : Expr := .binary .integerMul left right
private def idiv (left right : Expr) : Expr := .binary .integerDiv left right
private def imod (left right : Expr) : Expr := .binary .integerMod left right
private def either (first second : Expr) : Expr := .ifE first (.bool true) second
private def toWord (value : Expr) : Expr := .unary .integerToWord value
private def ofWord (value : Expr) : Expr := .unary .wordToInteger value

/-- The revert payload: its length and its bytes in two Words, zero past the
length. -/
def payloadType : Ty := .product .word (.product .word .word)

def resultType : Ty := .sum .word payloadType

def packet (length first second : Nat) : Expr := .pair (num length) (.pair (num first) (num second))

/-- `Panic(code)`: the selector `0x4e487b71`, then the code as a Word. -/
def panicPayload (code : Nat) : Expr := packet 36 (0x4e487b71 * 2 ^ 224) (code * 2 ^ 224)

/-- `DirtyHigherBitsForInteger()`, std's `Error(0x6cc54a63)`. -/
def dirtyPayload : Expr := packet 4 (0x6cc54a63 * 2 ^ 224) 0

private def raise (payload : Expr) : Expr := .inRight .word payload

/-- The reference's binders by de Bruijn level. -/
structure Env where
  depth : Nat
  inputs : List Nat := []
  amounts : List Nat := []
  vars : List Nat := []
  results : List Nat := []

namespace Env

def ref (env : Env) (level : Nat) : Expr := .var (env.depth - 1 - level)

/-- Bind a value and continue with its level. -/
def bind (env : Env) (value : Expr) (rest : Env → Nat → Expr) : Expr :=
  .letE value (rest {env with depth := env.depth + 1} env.depth)

end Env

/-- The input Word's level: the lambda's parameter. -/
private def inputLevel : Nat := 0

/-- A Word converted to the type as the source writes it. -/
def convertExpr (type : IntType) (word : Expr) : Expr :=
  if type.bytes = 32 then word
  else if type.signed then .binary .wordSignExtend (num (type.bytes - 1)) word
  else .binary .wordAnd word (num (2 ^ type.bits - 1))

def offsetExpr (word : Expr) (offset : Nat) : Expr :=
  if offset = 0 then word else .binary .wordAdd word (num offset)

/-- The integer a representation Word holds. -/
def readInt (type : IntType) (word : Expr) : Expr :=
  if type.signed then .ifE (.binary .wordGt word (num (2 ^ 255 - 1))) (isub (ofWord word) (int ((2 : Int) ^ 256)))
    (ofWord word)
  else ofWord word

def wrapExpr (type : IntType) (value : Expr) : Expr :=
  iadd (imod (isub value (int type.minimum)) (int ((2 : Int) ^ type.bits))) (int type.minimum)

def testExpr (word : Expr) : Test → Expr
  | .lt constant => .binary .wordGt (num constant) word
  | .gt constant => .binary .wordGt word (num constant)
  | .eq constant => .binary .wordEq word (num constant)
  | .bits mask value => .binary .wordEq (.binary .wordAnd word (num mask)) (num value)

/-- The quotient rounded toward zero: the floor quotient of the magnitudes,
negated when exactly one operand is negative. -/
def quotient (env : Env) (left right : Nat) (rest : Env → Nat → Expr) : Expr :=
  let magnitude (env : Env) (level : Nat) : Expr :=
    .ifE (ilt (env.ref level) (int 0)) (isub (int 0) (env.ref level)) (env.ref level)
  env.bind (idiv (magnitude env left) (magnitude env right)) fun env floor =>
    let negated := isub (int 0) (env.ref floor)
    env.bind (.ifE (ilt (env.ref left) (int 0))
      (.ifE (ilt (env.ref right) (int 0)) (env.ref floor) negated)
      (.ifE (ilt (env.ref right) (int 0)) negated (env.ref floor))) rest

/-- Range-check or wrap an exact result, then bind its representation Word. -/
def finish (type : IntType) (unchecked : Bool) (env : Env) (result : Nat) (rest : Env → Nat → Expr) : Expr :=
  if unchecked then env.bind (toWord (wrapExpr type (env.ref result))) rest
  else .ifE (either (ilt (env.ref result) (int type.minimum)) (ilt (int type.maximum) (env.ref result)))
    (raise (panicPayload 0x11)) (env.bind (toWord (env.ref result)) rest)

/-- An operation on two representation Words: a zero divisor panics with
`0x12`, then the exact result is range-checked or wrapped. -/
def operation (type : IntType) (unchecked : Bool) (op : Op) (env : Env) (left right : Env → Expr)
    (rest : Env → Nat → Expr) : Expr :=
  env.bind (readInt type (left env)) fun env first =>
  env.bind (readInt type (right env)) fun env second =>
    let compute (env : Env) : Expr := match op with
      | .add => env.bind (iadd (env.ref first) (env.ref second)) fun env result => finish type unchecked env result rest
      | .sub => env.bind (isub (env.ref first) (env.ref second)) fun env result => finish type unchecked env result rest
      | .mul => env.bind (imul (env.ref first) (env.ref second)) fun env result => finish type unchecked env result rest
      | .div => quotient env first second fun env result => finish type unchecked env result rest
      | .mod => quotient env first second fun env result =>
          env.bind (isub (env.ref first) (imul (env.ref second) (env.ref result))) fun env remainder =>
            finish type unchecked env remainder rest
    if op == .div || op == .mod then
      .ifE (.binary .integerEq (env.ref second) (int 0)) (raise (panicPayload 0x12)) (compute env)
    else compute env

def negation (type : IntType) (unchecked : Bool) (env : Env) (operand : Env → Expr) (rest : Env → Nat → Expr) :
    Expr :=
  env.bind (readInt type (operand env)) fun env value =>
  env.bind (isub (int 0) (env.ref value)) fun env result => finish type unchecked env result rest

/-- A shift of a representation Word by an amount Word: `2^s` is
`1 << s`, read as an integer, for an amount below 256. -/
def shiftExpr (type : IntType) (direction : Direction) (env : Env) (value amount : Env → Expr)
    (rest : Env → Nat → Expr) : Expr :=
  env.bind (readInt type (value env)) fun env first =>
  env.bind (amount env) fun env shift =>
    let power := ofWord (.binary .wordShl (num 1) (env.ref shift))
    match direction with
    | .left => env.bind (.ifE (.binary .wordGt (env.ref shift) (num (type.bits - 1))) (num 0)
        (toWord (wrapExpr type (imul (env.ref first) power)))) rest
    | .right => env.bind (.ifE (.binary .wordGt (env.ref shift) (num 255))
        (if type.signed then .ifE (ilt (env.ref first) (int 0)) (num (2 ^ 256 - 1)) (num 0) else num 0)
        (toWord (idiv (env.ref first) power))) rest

namespace Plan

def operandExpr (plan : Plan) (env : Env) : Operand → Expr
  | .input index => env.ref (env.inputs.getD index 0)
  | .var index => env.ref (env.vars.getD index 0)
  | .literal index => num (IntType.rep (plan.type.literals.getD index 0))

def amountExpr (env : Env) : Amount → Expr
  | .input index => env.ref (env.amounts.getD index 0)
  | .literal index => num (amountLiterals.getD index 0)

/-- Fold the results as the source does, then return the left injection. -/
def close (plan : Plan) (env : Env) : Expr :=
  let rec go (env : Env) (acc : Nat) : List Nat → Expr
    | [] => .inLeft payloadType (if plan.raw then convertExpr plan.type (env.ref acc) else env.ref acc)
    | result :: rest =>
        env.bind (.binary .wordXor (.binary .wordMul (env.ref acc) (num foldConstant)) (env.ref result))
          fun env acc => go env acc rest
  env.bind (num 0) fun env acc => go env acc env.results

def compile (plan : Plan) : Env → List (Bool × Step) → Expr
  | env, [] => plan.close env
  | env, (unchecked, step) :: rest =>
      let type := plan.type
      let next (isVar : Bool) (env : Env) (level : Nat) : Expr :=
        let vars := if isVar then env.vars ++ [level] else env.vars
        compile plan {env with vars, results := env.results ++ [level]} rest
      match step with
      | .assign (.binary op left right) | .assign (.compound op left right) =>
          operation type unchecked op env (plan.operandExpr · left) (plan.operandExpr · right) (next true)
      | .assign (.neg operand) => negation type unchecked env (plan.operandExpr · operand) (next true)
      | .assign (.call helper left right) =>
          let helper := plan.helpers.getD helper default
          operation type helper.unchecked helper.op env (plan.operandExpr · left) (plan.operandExpr · right)
            (next true)
      | .assign (.apply op body left right) =>
          operation type body op env (plan.operandExpr · left) (plan.operandExpr · right) (next true)
      | .default made =>
          let literal (index : Nat) : Expr := num (IntType.rep (IntType.uint256.literals.getD index 0))
          env.bind (.ifE (testExpr (env.ref inputLevel) made.test) (literal made.chosen) (literal made.initial))
            fun env chosen => operation IntType.uint256 unchecked made.op env (·.ref chosen)
              (fun _ => literal made.operand) (next false)
      | .shift shift =>
          shiftExpr type shift.direction env (plan.operandExpr · shift.value) (amountExpr · shift.amount)
            (next true)

/-- Bind the amounts `sc_k<j>`, then compile the steps. -/
def bindAmounts (plan : Plan) : Env → List AmountInput → Expr
  | env, [] => plan.compile env plan.steps
  | env, amount :: rest =>
      env.bind (convertExpr amount.type.type (offsetExpr (env.ref inputLevel) amount.offset))
        fun env level => plan.bindAmounts {env with amounts := env.amounts ++ [level]} rest

/-- Bind the inputs `sc_a<i>`: with `run(T)`, `sc_a0` is the argument. -/
def bindInputs (plan : Plan) : Env → List (Nat × Nat) → Expr
  | env, [] => plan.bindAmounts env plan.amounts
  | env, (offset, index) :: rest =>
      let word := if plan.abi && index = 0 then env.ref inputLevel
        else convertExpr plan.type (offsetExpr (env.ref inputLevel) offset)
      env.bind word fun env level => plan.bindInputs {env with inputs := env.inputs ++ [level]} rest

def body (plan : Plan) (env : Env) : Expr := plan.bindInputs env plan.inputs.zipIdx

/-- `fun input => …`: std's ABI check of a `run(T)` argument, the inputs and
amounts, every step with its helpers and lambdas inlined, then the left
injection of the folded Words; a panic or the ABI check's revert is the right
injection. -/
def expression (plan : Plan) : Expr :=
  let env : Env := {depth := 1}
  let body := plan.body env
  .lambda .word resultType (if plan.abi then
    .ifE (.binary .wordEq (convertExpr plan.type (env.ref inputLevel)) (env.ref inputLevel)) body
      (raise dirtyPayload)
    else body)

def program (plan : Plan) : Program := {
  resultType := .function .word resultType, dataDefinitions := [], body := plan.expression}

def applied (plan : Plan) (input : Word) : Program := {
  resultType, dataDefinitions := [], body := .apply plan.expression (.word input)}

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

end Plan

/-! Specified shapes: the plan's own values, and those its run reaches at the
eight boundary inputs, never measured on a compiled path. -/

/-- The eight boundary inputs of the primitive profile. -/
def boundaryWords : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

def Operand.shape : Operand → String
  | .input 0 => "input"
  | .input _ => "offset"
  | .var _ => "variable"
  | .literal _ => "literal"

def Form.operands : Form → List Operand
  | .binary _ left right | .compound _ left right | .call _ left right | .apply _ _ left right => [left, right]
  | .neg operand => [operand]

private def sorted (values : List String) : List String :=
  (values.foldl (fun seen value => if seen.contains value then seen else seen ++ [value]) []).mergeSort (· ≤ ·)

namespace Plan

def boundaryRuns (plan : Plan) : List (Outcome × List Event) := boundaryWords.map plan.run

def formName : Form → String
  | .binary .. | .neg _ => "inline"
  | .compound .. => "compound"
  | .call .. => "call"
  | .apply .. => "apply"

def opName (plan : Plan) : Form → String
  | .binary op _ _ | .compound op _ _ | .apply op _ _ _ => op.name
  | .neg _ => "neg"
  | .call helper _ _ => (plan.helpers.getD helper default).op.name

/-- An operation's own context: a helper's or lambda body's scope, otherwise
its group's. -/
def context (plan : Plan) (unchecked : Bool) : Form → Bool
  | .call helper _ _ => (plan.helpers.getD helper default).unchecked
  | .apply _ body _ _ => body
  | _ => unchecked

def scope (plan : Plan) (unchecked : Bool) : Step → List String
  | .assign (.call helper _ _) =>
      if (plan.helpers.getD helper default).unchecked then ["unchecked-helper"]
      else if unchecked then ["call-in-block"] else []
  | .assign (.apply _ body _ _) => if body then ["unchecked-lambda"] else if unchecked then ["apply-in-block"] else []
  | .assign _ | .default _ => if unchecked then ["block"] else []
  | .shift _ => []

def literalShapes (plan : Plan) (operands : List Operand) : List String :=
  operands.filterMap fun operand => match operand with
    | .literal index => some (plan.type.literalClass index)
    | _ => none

def outcomeName : Outcome → String
  | .word _ => "returned"
  | .panic 0x11 => "panic-0x11"
  | .panic _ => "panic-0x12"
  | .dirty => "dirty"

def panicName : Event → Option String
  | .panic "div" unchecked _ 0x12 => some (if unchecked then "unchecked-div-zero" else "div-zero")
  | .panic "mod" unchecked _ _ => some (if unchecked then "unchecked-mod-zero" else "mod-zero")
  | .panic "div" _ _ _ => some "div-overflow"
  | .panic name _ _ _ => some name
  | _ => none

def typeOutcome (plan : Plan) : Event → Option String
  | .panic _ _ true code => some (plan.type.name ++ (if code == 0x11 then ":0x11" else ":0x12"))
  | .operation _ _ true true => some (plan.type.name ++ ":wrap")
  | _ => none

/-- The `runtime-checked-arithmetic` shapes. -/
def arithmeticShapes (plan : Plan) : List (String × List String) :=
  let steps := plan.steps
  let forms := steps.filterMap fun (_, step) => match step with
    | .assign form => some form
    | _ => none
  let operands := forms.flatMap Form.operands
  let runs := plan.boundaryRuns
  let events := runs.flatMap (·.2)
  [("types", [plan.type.name]),
    ("operators", sorted (steps.map fun (_, step) => match step with
      | .assign form => plan.opName form
      | .default made => made.op.name
      | .shift _ => "")),
    ("forms", sorted (steps.map fun (_, step) => match step with
      | .assign form => formName form
      | _ => "default")),
    ("contexts", sorted (steps.map fun (unchecked, step) =>
      let context := match step with
        | .assign form => plan.context unchecked form
        | _ => unchecked
      if context then "unchecked" else "checked")),
    ("scopes", sorted (steps.flatMap fun (unchecked, step) => plan.scope unchecked step)),
    ("operands", sorted (operands.map Operand.shape)),
    ("literals", sorted (plan.literalShapes operands)),
    ("parameters", [if plan.abi then "abi" else "word"]),
    ("returns", [if plan.raw then "raw" else "word"]),
    ("outcomes", sorted (runs.map fun (outcome, _) => outcomeName outcome)),
    ("panics", sorted (events.filterMap panicName)),
    ("wraps", sorted (events.filterMap fun event => match event with
      | .operation name true _ true => some name
      | _ => none)),
    ("typeOutcomes", sorted (events.filterMap plan.typeOutcome ++
      runs.filterMap fun (outcome, _) => if outcome == .dirty then some (plan.type.name ++ ":dirty") else none))]

def rangeName (bits amount : Nat) : String :=
  if amount = 0 then "zero" else if amount + 1 < bits then "inside" else if amount + 1 = bits then "last"
  else if amount = bits then "width" else if amount < 256 then "beyond" else "huge"

/-- The `runtime-shifts` shapes. -/
def shiftShapes (plan : Plan) : List (String × List String) :=
  let shifts := plan.steps.filterMap fun (unchecked, step) => match step with
    | .shift shift => some (unchecked, shift)
    | _ => none
  let bits := plan.type.bits
  let events := plan.boundaryRuns.flatMap (·.2)
  let reached := events.filterMap fun event => match event with
    | .shift _ amount result => some (amount, result)
    | _ => none
  [("values", [plan.value.name]),
    ("amounts", sorted (shifts.map fun (_, shift) => match shift.amount with
      | .input index => ((plan.amounts.getD index default).type).name
      | .literal _ => "literal")),
    ("operators", sorted (shifts.map fun (_, shift) => shift.direction.name plan.value)),
    ("forms", sorted (shifts.map fun (_, shift) => if shift.compound then "compound" else "inline")),
    ("contexts", sorted (shifts.map fun (unchecked, _) => if unchecked then "unchecked" else "checked")),
    ("operands", sorted (shifts.map fun (_, shift) => shift.value.shape)),
    ("ranges", sorted (reached.map fun (amount, _) => rangeName bits amount)),
    ("results", sorted (reached.filterMap fun (amount, result) =>
      if amount < bits then none else if result == 0 then some "zero" else if result == -1 then some "minus-one"
      else none)),
    ("typeRanges", sorted (reached.filterMap fun (amount, _) =>
      if bits ≤ amount then some (plan.value.name ++ ":width") else none))]

end Plan

/-- Every value of each checked arithmetic shape dimension. -/
def arithmeticShapeInventory : List (String × List String) :=
  let types := IntType.all.map (·.name)
  [("types", sorted types), ("operators", ["add", "div", "mod", "mul", "neg", "sub"]),
    ("forms", ["apply", "call", "compound", "default", "inline"]), ("contexts", ["checked", "unchecked"]),
    ("scopes", ["apply-in-block", "block", "call-in-block", "unchecked-helper", "unchecked-lambda"]),
    ("operands", ["input", "literal", "offset", "variable"]),
    ("literals", ["half", "max", "max1", "min", "min1", "minus1", "one", "small", "zero"]),
    ("parameters", ["abi", "word"]), ("returns", ["raw", "word"]),
    ("outcomes", ["dirty", "panic-0x11", "panic-0x12", "returned"]),
    ("panics", ["add", "div-overflow", "div-zero", "mod-zero", "mul", "neg", "sub", "unchecked-div-zero",
      "unchecked-mod-zero"]),
    ("wraps", ["add", "div", "mul", "neg", "sub"]),
    ("typeOutcomes", sorted (types.flatMap fun name =>
      [name ++ ":0x11", name ++ ":0x12", name ++ ":wrap"] ++ (if name.endsWith "256" then [] else [name ++ ":dirty"])))]

/-- Every value of each shift shape dimension. -/
def shiftShapeInventory : List (String × List String) :=
  let values := ValueType.all.map (·.name)
  [("values", sorted values), ("amounts", sorted ("literal" :: ValueType.amounts.map (·.name))),
    ("operators", ["sar", "shl", "shr"]), ("forms", ["compound", "inline"]), ("contexts", ["checked", "unchecked"]),
    ("operands", ["input", "literal", "offset", "variable"]),
    ("ranges", ["beyond", "huge", "inside", "last", "width", "zero"]), ("results", ["minus-one", "zero"]),
    ("typeRanges", sorted (values.map (· ++ ":width")))]

/-! Reconstruction and fitting. -/

/-- Consecutive steps of one context in one group; past the third block, a
block's steps join the checked context. -/
def regroup (steps : List (Bool × Step)) : List Group := Id.run do
  let mut groups : List Group := []
  let mut blocks := 0
  for (unchecked, step) in steps do
    let unchecked := unchecked && (blocks < 3 || (groups.getLast?.map (·.unchecked)).getD false)
    match groups.getLast? with
    | some last =>
        if last.unchecked == unchecked then
          groups := groups.dropLast ++ [{last with steps := last.steps ++ [step]}]
        else
          if unchecked then blocks := blocks + 1
          groups := groups ++ [{unchecked, steps := [step]}]
    | none =>
        if unchecked then blocks := blocks + 1
        groups := groups ++ [{unchecked, steps := [step]}]
  return groups

namespace Plan

/-- Remove the helpers no call names, renumbering the calls. -/
def pruned (plan : Plan) : Plan :=
  let called := plan.calledHelpers
  let kept := (List.range plan.helpers.length).filter called.contains
  let renumber (index : Nat) : Nat := (kept.idxOf? index).getD 0
  let step : Step → Step
    | .assign (.call helper left right) => .assign (.call (renumber helper) left right)
    | other => other
  let groups := plan.groups.map fun group => {group with steps := group.steps.map step}
  {plan with helpers := kept.filterMap (plan.helpers[·]?), groups}

def withSteps (plan : Plan) (steps : List (Bool × Step)) : Plan := ({plan with groups := regroup steps}).pruned

/-- Steps are dropped from the end while the reference exceeds the budget and
more than one step remains. -/
def fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range 10 do
    if plan.nodes > nodes && plan.stepCount > 1 then plan := plan.withSteps plan.steps.dropLast
  return plan

end Plan

/-! Generation: a SplitMix64 stream of the case seed, one domain per
profile. -/

def arithmeticDomain : UInt64 := 0x636865636b000001
def shiftDomain : UInt64 := 0x7368696674000001

/-- An input 4, a variable 4 when one exists, or a literal by its weight. -/
def drawOperand (type : IntType) (inputs vars literal : Nat) : Gen Operand := do
  match ← drawWeighted [4, if vars = 0 then 0 else 4, literal] with
  | 0 => return .input (← draw inputs)
  | 1 => return .var (← draw vars)
  | _ => return .literal (← draw type.literals.length)

def drawTest : Gen Test := do
  let constant := testConstants.getD (← draw testConstants.length) 0
  match ← draw 4 with
  | 0 => return .lt constant
  | 1 => return .gt constant
  | 2 => return .eq constant
  | _ =>
      let mask := testMasks.getD (← draw testMasks.length) 1
      return .bits mask (← draw (mask + 1))

/-- A divisor is a literal less often, so that inputs reach zero. -/
def drawRight (type : IntType) (inputs vars : Nat) (op : Op) : Gen Operand :=
  drawOperand type inputs vars (if op == .div || op == .mod then 2 else 4)

/-- A third of a signed division's operands are `MIN / -1` where an input
reaches `MIN` at a boundary input: the input offset by `2^(bits - 1)`, or the
`MIN` literal, by the `-1` literal. -/
def drawOperands (type : IntType) (offsets : List Nat) (vars : Nat) (op : Op) : Gen (Operand × Operand) := do
  let extreme := (← draw 3) == 0
  if type.signed && op == .div && extreme then
    let left := match offsets.idxOf? (2 ^ (type.bits - 1)) with
      | some index => Operand.input index
      | none => Operand.literal 0
    return (left, .literal 2)
  else return (← drawOperand type offsets.length vars 2, ← drawRight type offsets.length vars op)

def drawForm (type : IntType) (helpers : List Helper) (offsets : List Nat) (vars : Nat) (unchecked : Bool) :
    Gen Form := do
  let op := Op.all.getD (← draw 5) .add
  let inputs := offsets.length
  match ← drawWeighted [6, 2, 2, if helpers.isEmpty then 0 else 3, 2] with
  | 0 => let (left, right) ← drawOperands type offsets vars op; return .binary op left right
  | 1 =>
      if vars = 0 || (← draw 2) == 0 then return .neg (.input (← draw inputs))
      else return .neg (.var (← draw vars))
  | 2 => let (left, right) ← drawOperands type offsets vars op; return .compound op left right
  | 3 =>
      let helper ← draw helpers.length
      let callee := (helpers.getD helper default).op
      let (left, right) ← drawOperands type offsets vars callee
      return .call helper left right
  | _ =>
      let body := !unchecked && (← draw 2) == 0
      let (left, right) ← drawOperands type offsets vars op
      return .apply op body left right

def drawDefault : Gen Default := do
  let count := IntType.uint256.literals.length
  let initial ← draw count
  let test ← drawTest
  let chosen ← draw count
  let op := Op.all.getD (← draw 5) .add
  return {initial, test, chosen, op, operand := ← draw count}

def drawInputs (type : IntType) : Gen (List Nat) := do
  let count := 1 + (← draw 3)
  let mut inputs := [0]
  for _ in List.range (count - 1) do
    inputs := inputs ++ [type.offsets.getD (1 + (← draw (type.offsets.length - 1))) 0]
  return inputs

/-- A `runtime-checked-arithmetic` plan: a type, then the parameter and result
forms, one to three inputs, zero to two helpers and three to ten steps, a
third of them in blocks when the plan has blocks. -/
def drawArithmetic : Gen Plan := do
  let type := IntType.all.getD (← draw IntType.all.length) default
  let abi := (← draw 4) == 0
  let raw := type.bytes < 32 && (← draw 4) == 0
  let inputs ← drawInputs type
  let mut helpers : List Helper := []
  for _ in List.range (← drawWeighted [3, 2, 1]) do
    let op := Op.all.getD (← draw 5) .add
    helpers := helpers ++ [{op, unchecked := (← draw 2) == 0}]
  let blocks := (← draw 3) != 0
  let mut steps : List (Bool × Step) := []
  let mut vars := 0
  let mut defaults := 0
  for _ in List.range (3 + (← draw 8)) do
    let unchecked := blocks && (← draw 3) == 0
    if defaults < 2 && (← draw 10) == 0 then
      steps := steps ++ [(unchecked, .default (← drawDefault))]
      defaults := defaults + 1
    else
      steps := steps ++ [(unchecked, .assign (← drawForm type helpers inputs vars unchecked))]
      vars := vars + 1
  return ({value := .int type, abi, raw, inputs, amounts := [], helpers, groups := []} : Plan).withSteps steps

/-- A `runtime-shifts` plan: a value type, one to three inputs, one to three
amounts and two to eight shifts, half of them in blocks when the plan has
blocks. -/
def drawShifts : Gen Plan := do
  let value := ValueType.all.getD (← draw ValueType.all.length) .word
  let type := value.type
  let inputs ← drawInputs type
  let mut amounts : List AmountInput := []
  for _ in List.range (1 + (← draw 3)) do
    let amountType := ValueType.amounts.getD (← draw ValueType.amounts.length) .word
    amounts := amounts ++ [{type := amountType, offset := amountOffsets.getD (← draw amountOffsets.length) 0}]
  let blocks := (← draw 4) == 0
  let mut steps : List (Bool × Step) := []
  let mut vars := 0
  for _ in List.range (2 + (← draw 7)) do
    let unchecked := blocks && (← draw 2) == 0
    let direction := if (← draw 2) == 0 then Direction.left else .right
    let compound := (← draw 4) == 0
    let operand ← drawOperand type inputs.length vars 2
    let amount ← if (← draw 10) < 7 then do pure (Amount.input (← draw amounts.length))
      else do pure (Amount.literal (← draw amountLiterals.length))
    steps := steps ++ [(unchecked, .shift {direction, compound, value := operand, amount})]
    vars := vars + 1
  return ({value, abi := false, raw := false, inputs, amounts, helpers := [], groups := []} : Plan).withSteps steps

def generateArithmetic (seed : UInt64) : Plan :=
  Id.run (drawArithmetic.run' {seed, domain := arithmeticDomain, index := 0})

def generateShifts (seed : UInt64) : Plan :=
  Id.run (drawShifts.run' {seed, domain := shiftDomain, index := 0})

end Solcore.Synthesis.Core.Integers
