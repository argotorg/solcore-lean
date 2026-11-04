import Solcore.Synthesis.Core.EnumData
import Solcore.Frontend.RustHull.Precompiles
import Solcore.Core.Wire.Codec.Program
import Solcore.Synthesis.Source.Emitter
import Solcore.Synthesis.Internal.Enums

/-!
# Profile: memory values

The profile `runtime-memory-values`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.MemoryValues
/-! Solcore-level memory values in pure functions, the plans of the
`runtime-memory-values` profile: `memory<bytes>` values built from Words with
std's `to_bytes`, `concat` and `empty`, slices (`memory_ref`) taken with
`slice_` and `truncate`, Word arrays (`memory<DynArray<uint256>>`), second
variables, writes inline or through helpers, lengths, Word and byte reads
through std's range checks, element reads and `keccak256_`, in straight-line
code and inside the bounded `while` forms.

The original Core reference models every value abstractly, as its byte list:
a static length and the bytes packed big-endian into at most four Words, zero
past the length. A slice is a start and a length over the value it was taken
from, and a second variable names the same value, so writes are seen through
every variable and slice of a value and never through a copy. An array is its
elements. No address, length header, free-memory pointer or std function
appears in the reference. An out-of-range access makes it return the right
injection of its failure's code: std's `OutOfBounds()` revert for a value's
Words and bytes, read and written through `slice_` and `truncate`, and since
solcore-rs `e2eef194` std's `Panic(0x32)` for an array element. Nothing here
reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryValues

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)
open Solcore.Frontend.RustHull

def memoryVersion : String := "core-memory-values-v2"

/-- A Word of the source: the input, the input with a constant, the
accumulator `sc_r`, or the loop's position. -/
inductive Operand where
  | input
  | add (constant : Nat)
  | mul (constant : Nat)
  | xor (constant : Nat)
  | acc
  | counter
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An index: a literal, `mod(shr(shift, sc_x), modulus)`, or
`((P * scale) + offset)` over the loop's position `P`. -/
inductive Index where
  | literal (value : Nat)
  | input (shift modulus : Nat)
  | counter (scale offset : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A variable by kind and declaration number: `sc_b<n>`, `sc_s<n>`, `sc_a<n>`. -/
inductive Ref where
  | bytes (number : Nat)
  | slice (number : Nat)
  | array (number : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A part of a built value: `bytes32(W)`, `empty(n)`, or a bytes value or
slice. -/
inductive Part where
  | word (operand : Operand)
  | zeros (count : Nat)
  | value (ref : Ref)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Build where
  | toBytes (part : Part)
  | concat (left right : Part)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `slice_(v, start)`, `truncate(v, length)` or
`truncate(slice_(v, start), length)`. -/
inductive Cut where
  | drop (start : Nat)
  | take (length : Nat)
  | window (start length : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Width where
  | word
  | byte
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Form where
  | inline
  | helper
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Fold where
  | add
  | xor
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An observation of a value: its length, a Word or byte at an index, its
hash, or an array element by `a[i]` or by `IndexAccess.get`. -/
inductive Access where
  | length
  | word (index : Index)
  | byte (index : Index)
  | hash
  | element (index : Index) (get : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Action where
  | bytes (build : Build)
  | slice (source : Ref) (cut : Cut)
  | alias (source : Ref)
  | array (allocated : Bool) (elements : List Operand)
  | write (target : Ref) (index : Index) (value : Operand) (width : Width) (form : Form)
  | observe (fold : Fold) (constant : Nat) (value : Ref) (access : Access)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The inner bound of a nested loop: `(sc_x & m)` or `((sc_i + 1) & m)`. -/
inductive Bound where
  | input
  | counter
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Loop where
  | single (mask : Nat)
  | nested (outer : Nat) (bound : Bound) (inner : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Step where
  | action (action : Action)
  | loop (loop : Loop) (body : List Action)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  steps : List Step
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Bounds. -/

def maximumSteps : Nat := 10
def maximumBody : Nat := 3
def maximumLength : Nat := 128
def maximumZeros : Nat := 40
def maximumElements : Nat := 4
def maximumBytes : Nat := 4
def maximumSlices : Nat := 3
def maximumArrays : Nat := 2
def maximumHashes : Nat := 7
def shifts : List Nat := [0, 1, 3, 8, 128, 252]
def scales : List Nat := [1, 2, 3, 11, 32]
def maximumOffset : Nat := 8
def indexSlack : Nat := 8
def foldConstants : List Nat := (List.range 15).map fun index => 2 * index + 3
def singleMasks : List Nat := [1, 3, 7]
def nestedMasks : List Nat := [1, 3]

namespace Ref

def isArray : Ref → Bool
  | .array _ => true
  | _ => false

def isSlice : Ref → Bool
  | .slice _ => true
  | _ => false

def number : Ref → Nat
  | .bytes number | .slice number | .array number => number

end Ref

def Operand.admitted (inLoop : Bool) : Operand → Bool
  | .input | .acc => true
  | .add constant | .xor constant => 1 ≤ constant && constant ≤ 255
  | .mul constant => 2 ≤ constant && constant ≤ 255
  | .counter => inLoop

/-- `valid` is the number of in-range positions, at least one. -/
def Index.admitted (inLoop : Bool) (valid : Nat) : Index → Bool
  | .literal value => value < valid
  | .input shift modulus => shifts.contains shift && 1 ≤ modulus && modulus ≤ valid + indexSlack
  | .counter scale offset => inLoop && scales.contains scale && offset ≤ maximumOffset

def Index.dynamic : Index → Bool
  | .literal _ => false
  | _ => true

/-- In-range positions of a Word or byte access to `length` bytes. -/
def Width.valid? (width : Width) (length : Nat) : Option Nat :=
  match width with
  | .word => if 32 ≤ length then some (length - 31) else none
  | .byte => if 1 ≤ length then some length else none

def Cut.apply? (length : Nat) : Cut → Option (Nat × Nat)
  | .drop start => if start ≤ length then some (start, length - start) else none
  | .take kept => if kept ≤ length then some (0, kept) else none
  | .window start kept => if start + kept ≤ length then some (start, kept) else none

def Loop.admitted : Loop → Bool
  | .single mask => singleMasks.contains mask
  | .nested outer _ inner => nestedMasks.contains outer && nestedMasks.contains inner

/-- The most iterations of the innermost body on any input. -/
def Loop.trips : Loop → Nat
  | .single mask => mask
  | .nested outer _ inner => outer * inner

/-! The static scope: what each declaration binds. -/

/-- A variable's value, the start of its bytes in the value and its length in
bytes, or an array's value and element count. -/
structure Var where
  object : Nat
  start : Nat
  length : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Declared variables by kind and number, `none` once out of scope, and the
values in creation order: `(true, count)` for an array, `(false, length)` for
bytes. -/
structure Scope where
  bytes : List (Option Var) := []
  slices : List (Option Var) := []
  arrays : List (Option Var) := []
  objects : List (Bool × Nat) := []
  deriving Repr, BEq, Inhabited

namespace Scope

def var? (scope : Scope) : Ref → Option Var
  | .bytes number => (scope.bytes[number]?).join
  | .slice number => (scope.slices[number]?).join
  | .array number => (scope.arrays[number]?).join

def visible (scope : Scope) : List Ref :=
  (scope.bytes.zipIdx.filterMap fun (var, number) => var.map fun _ => Ref.bytes number) ++
  (scope.slices.zipIdx.filterMap fun (var, number) => var.map fun _ => Ref.slice number) ++
  (scope.arrays.zipIdx.filterMap fun (var, number) => var.map fun _ => Ref.array number)

private def need (condition : Bool) : Option Unit := if condition then some () else none

def partLength? (scope : Scope) (inLoop : Bool) : Part → Option Nat
  | .word operand => if operand.admitted inLoop then some 32 else none
  | .zeros count => if count ≤ maximumZeros then some count else none
  | .value ref => if ref.isArray then none else (scope.var? ref).map (·.length)

def buildLength? (scope : Scope) (inLoop : Bool) : Build → Option Nat
  | .toBytes part => partLength? scope inLoop part
  | .concat left right => do
      return (← partLength? scope inLoop left) + (← partLength? scope inLoop right)

/-- The in-range positions of an access to a variable, if it has any. -/
def accessValid? (ref : Ref) (var : Var) : Access → Option Nat
  | .length | .hash => if ref.isArray then none else some 1
  | .word _ => if ref.isArray then none else Width.valid? .word var.length
  | .byte _ => if ref.isArray then none else Width.valid? .byte var.length
  | .element _ _ => if ref.isArray then some var.length else none

def Access.index? : Access → Option Index
  | .word index | .byte index | .element index _ => some index
  | _ => none

/-- The scope after an admitted action, or `none`. -/
def step? (scope : Scope) (inLoop : Bool) : Action → Option Scope
  | .bytes build => do
      let length ← buildLength? scope inLoop build
      need (length ≤ maximumLength && scope.bytes.length < maximumBytes)
      let object := scope.objects.length
      return {scope with objects := scope.objects ++ [(false, length)],
                         bytes := scope.bytes ++ [some {object, start := 0, length}]}
  | .slice source cut => do
      need (!source.isArray && scope.slices.length < maximumSlices)
      let var ← scope.var? source
      let (start, length) ← cut.apply? var.length
      return {scope with slices := scope.slices ++ [some {var with start := var.start + start, length}]}
  | .alias source => do
      need !inLoop
      let var ← scope.var? source
      match source with
      | .bytes _ =>
          need (scope.bytes.length < maximumBytes)
          return {scope with bytes := scope.bytes ++ [some var]}
      | .array _ =>
          need (scope.arrays.length < maximumArrays)
          return {scope with arrays := scope.arrays ++ [some var]}
      | .slice _ => none
  | .array _ elements => do
      need (1 ≤ elements.length && elements.length ≤ maximumElements &&
        elements.all (·.admitted inLoop) && scope.arrays.length < maximumArrays)
      let object := scope.objects.length
      return {scope with objects := scope.objects ++ [(true, elements.length)],
                         arrays := scope.arrays ++ [some {object, start := 0, length := elements.length}]}
  | .write target index value width _ => do
      let var ← scope.var? target
      need (value.admitted inLoop)
      let valid ← if target.isArray then (if width == .word then some var.length else none)
        else width.valid? var.length
      need (index.admitted inLoop valid)
      return scope
  | .observe _ constant value access => do
      need (foldConstants.contains constant)
      let var ← scope.var? value
      let valid ← accessValid? value var access
      need ((Access.index? access).all (·.admitted inLoop valid))
      return scope

private def hide (current previous : List (Option Var)) : List (Option Var) :=
  previous ++ (current.drop previous.length).map fun _ => none

/-- Variables declared since `outer` go out of scope; values stay. -/
def close (scope outer : Scope) : Scope :=
  {scope with bytes := hide scope.bytes outer.bytes, slices := hide scope.slices outer.slices,
              arrays := hide scope.arrays outer.arrays}

end Scope

def Step.loop? : Step → Option (Loop × List Action)
  | .loop shape body => some (shape, body)
  | .action _ => none

def Step.actions : Step → List Action
  | .action single => [single]
  | .loop _ body => body

def Action.hashes : Action → Bool
  | .observe _ _ _ .hash => true
  | _ => false

def Action.observes : Action → Bool
  | .observe .. => true
  | _ => false

def Step.hashCount : Step → Nat
  | .action single => if single.hashes then 1 else 0
  | .loop shape body => shape.trips * (body.filter (·.hashes)).length

namespace Plan

def hashCount (plan : Plan) : Nat := (plan.steps.map (·.hashCount)).sum
def hashes (plan : Plan) : Bool := plan.steps.any fun step => step.actions.any (·.hashes)

/-- The scope after every step, if each is admitted. -/
def scan? (plan : Plan) : Option Scope :=
  plan.steps.foldlM (init := ({} : Scope)) fun scope step =>
    match step with
    | .action action => scope.step? false action
    | .loop loop body => do
        if !(loop.admitted && 1 ≤ body.length && body.length ≤ maximumBody) then none
        let inner ← body.foldlM (fun current action => current.step? true action) scope
        return inner.close scope

def admitted (plan : Plan) : Bool :=
  1 ≤ plan.steps.length && plan.steps.length ≤ maximumSteps &&
  (plan.steps.filter (·.loop?.isSome)).length ≤ 1 &&
  plan.steps.any (fun step => step.actions.any (·.observes)) &&
  plan.hashCount ≤ maximumHashes && plan.scan?.isSome

end Plan

/-! Core expressions. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def sub (left right : Expr) : Expr := .binary .wordSub left right
private def mul (left right : Expr) : Expr := .binary .wordMul left right
private def band (left right : Expr) : Expr := .binary .wordAnd left right
private def bor (left right : Expr) : Expr := .binary .wordOr left right
private def bxor (left right : Expr) : Expr := .binary .wordXor left right
private def shl (value shift : Expr) : Expr := .binary .wordShl value shift
private def shr (value shift : Expr) : Expr := .binary .wordShr value shift
private def gt (left right : Expr) : Expr := .binary .wordGt left right
private def eq (left right : Expr) : Expr := .binary .wordEq left right
private def bnot (value : Expr) : Expr := .unary .wordNot value

def maximumWord : Nat := 2 ^ 256 - 1

/-- The first `count` bytes of a Word. -/
def high (count : Nat) : Nat := 2 ^ 256 - 2 ^ (8 * (32 - count))

def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)

def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value else field (index - 1) (count + 1) (.second value)

def words (count : Nat) : Ty :=
  match count with
  | 0 => .unit
  | 1 => .word
  | count + 2 => .product .word (words (count + 1))

/-! The hash closure: Keccak-256 of the first `length` bytes of four Words,
for every length up to 128, bytes past the length being zero. -/

private structure Lets where
  size : Nat
  bindings : Array Solcore.Core.Expr := #[]

private def Lets.ref (lets : Lets) (position : Nat) : Solcore.Core.Expr := .var (lets.size - 1 - position)

private def Lets.bind (lets : Lets) (value : Solcore.Core.Expr) : Lets × Nat :=
  ({lets with size := lets.size + 1, bindings := lets.bindings.push value}, lets.size)

private def Lets.close (lets : Lets) (body : Solcore.Core.Expr) : Solcore.Core.Expr :=
  lets.bindings.foldr (fun value rest => .letE value rest) body

/-- The low `width` bytes of every `2 * width`-byte group of a Word. -/
def swapMask (width : Nat) : Nat :=
  ((List.range 32).filter fun position => (position / width) % 2 = 0).foldl
    (fun mask position => mask + 255 * 2 ^ (8 * position)) 0

private def coreNumber (value : Nat) : Solcore.Core.Expr := .word (Word.ofNatModulo value)

private def coreBinary (op : Solcore.Core.BinaryOp) (left right : Solcore.Core.Expr) : Solcore.Core.Expr :=
  .binary op left right

/-- `fun (length, w0, w1, w2, w3) => keccak256` of the first `length` bytes of
`w0 ++ w1 ++ w2 ++ w3`: each Word byte-reversed by five group swaps so that
its four 64-bit lanes are shifts of it, Ethereum's `0x01` at offset `length`
and `0x80` at offset 135, then the Core Keccak-f[1600] permutation and digest
of the Hull import path. -/
def coreHash : Solcore.Core.Expr := Id.run do
  let mut lets : Lets := {size := 1}
  let mut parts : Array Nat := #[]
  for index in List.range 5 do
    let (next, position) := lets.bind (Keccak.field index 5 (lets.ref 0))
    lets := next
    parts := parts.push position
  let mut reversed : Array Nat := #[]
  for index in [1, 2, 3, 4] do
    let mut current := parts[index]!
    for width in [1, 2, 4, 8, 16] do
      let value := lets.ref current
      let mask := coreNumber (swapMask width)
      let (next, position) := lets.bind (coreBinary .wordOr
        (coreBinary .wordAnd (coreBinary .wordShr value (coreNumber (8 * width))) mask)
        (coreBinary .wordShl (coreBinary .wordAnd value mask) (coreNumber (8 * width))))
      lets := next
      current := position
    reversed := reversed.push current
  let (next, quotient) := lets.bind (coreBinary .wordShr (lets.ref parts[0]!) (coreNumber 3))
  lets := next
  let (next, padding) := lets.bind (coreBinary .wordShl (coreNumber 1)
    (coreBinary .wordShl (coreBinary .wordAnd (lets.ref parts[0]!) (coreNumber 7)) (coreNumber 3)))
  lets := next
  let pad := fun (lane : Nat) =>
    Solcore.Core.Expr.ifE (coreBinary .wordEq (lets.ref quotient) (coreNumber lane)) (lets.ref padding) (coreNumber 0)
  let lanes := (List.range 25).map fun lane =>
    if lane < 16 then
      coreBinary .wordXor
        (coreBinary .wordAnd (coreBinary .wordShr (lets.ref reversed[lane / 4]!) (coreNumber (64 * (lane % 4))))
          (coreNumber (2 ^ 64 - 1)))
        (pad lane)
    else if lane = 16 then coreBinary .wordXor (pad 16) (coreNumber (2 ^ 63))
    else coreNumber 0
  return .lambda (Keccak.types (List.replicate 5 .word)) .word
    (lets.close (.letE (Keccak.permute (Keccak.packet lanes)) (Keccak.digest (.var 0))))

/-- The closure as a Wire expression. A failed conversion would leave an
ill-typed `Unit` that full admission rejects, never a different hash. -/
def hashClosure : Expr := (Expr.ofCore? coreHash).getD .unit

def hashNodes : Nat := exprNodes hashClosure

/-! The reference compiler. Positions count every binding from the input
parameter; a reference to a position is valid in later initializers, checks
and the final body of the scope that bound it and of scopes it encloses. -/

/-- An out-of-range access's failure, which std observes as `OutOfBounds()`
for a value's Words and bytes and as `Panic(0x32)` for an array element. -/
inductive Failure where
  | bytes
  | array
  deriving BEq, Repr

/-- The Word a failure returns in the right injection. -/
def Failure.code : Failure → Nat
  | .bytes => 0
  | .array => 1

/-- A binding, a check that returns its failure's code in the scope's right
injection when its condition holds, or a case that continues with a left
injection's payload and forwards a right one's. -/
inductive Item where
  | bind (value : Expr)
  | fail (condition : Expr) (failure : Failure)
  | unpack (scrutinee : Expr)

structure Builder where
  size : Nat
  items : Array Item := #[]

namespace Builder

def ref (builder : Builder) (position : Nat) : Expr := .var (builder.size - 1 - position)

/-- The scope's items around `body`, in a scope whose result is the sum of
`left` and what its right injections carry, a failure code here. -/
def close (builder : Builder) (body : Expr) (left : Ty) : Expr :=
  builder.items.foldr (fun item rest => match item with
    | .bind value => .letE value rest
    | .fail condition failure => .ifE condition (.inRight left (num failure.code)) rest
    | .unpack scrutinee => .caseE scrutinee rest (.inRight left (.var 0))) body

end Builder

/-- The compiler's state: the builder, the static scope, the positions of
every value's Words or elements, the accumulator, the input, the hash
closure, the loop's position and the left type of the scope's result. -/
structure State where
  builder : Builder
  scope : Scope := {}
  values : Array (List Nat) := #[]
  acc : Nat := 0
  input : Nat := 0
  hash : Option Nat := none
  counter : Option Nat := none
  left : Ty := .word

namespace State

def ref (state : State) (position : Nat) : Expr := state.builder.ref position

def bind (state : State) (value : Expr) : State × Nat :=
  ({state with builder := {state.builder with size := state.builder.size + 1,
                                              items := state.builder.items.push (.bind value)}},
   state.builder.size)

def fail (state : State) (condition : Expr) (failure : Failure) : State :=
  {state with builder := {state.builder with items := state.builder.items.push (.fail condition failure)}}

def unpack (state : State) (scrutinee : Expr) : State × Nat :=
  ({state with builder := {state.builder with size := state.builder.size + 1,
                                              items := state.builder.items.push (.unpack scrutinee)}},
   state.builder.size)

/-- Bind values in order, each built at its own binding. -/
def bindAll (state : State) (values : List (State → Expr)) : State × List Nat :=
  values.foldl (fun (state, positions) value =>
    let (state, position) := state.bind (value state)
    (state, positions ++ [position])) (state, [])

def position (state : State) : Expr :=
  match state.counter with
  | some position => state.ref position
  | none => num 0

def operand (state : State) : Operand → Expr
  | .input => state.ref state.input
  | .add constant => add (state.ref state.input) (num constant)
  | .mul constant => mul (state.ref state.input) (num constant)
  | .xor constant => bxor (state.ref state.input) (num constant)
  | .acc => state.ref state.acc
  | .counter => state.position

def index (state : State) : Index → Expr
  | .literal value => num value
  | .input shift modulus => .binary .wordMod (shr (state.ref state.input) (num shift)) (num modulus)
  | .counter scale offset =>
      let scaled := if scale = 1 then state.position else mul state.position (num scale)
      if offset = 0 then scaled else add scaled (num offset)

def wordsOf (state : State) (object : Nat) : List Nat := state.values[object]?.getD []

def wordAt (state : State) (object index : Nat) : Expr :=
  match (state.wordsOf object)[index]? with
  | some position => state.ref position
  | none => num 0

/-- The Word at byte `offset` of a value. -/
def load (state : State) (object offset : Nat) : Expr :=
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then state.wordAt object index
  else if index + 1 < (state.wordsOf object).length then
    bor (shl (state.wordAt object index) (num (8 * delta))) (shr (state.wordAt object (index + 1)) (num (8 * (32 - delta))))
  else shl (state.wordAt object index) (num (8 * delta))

/-- The Words of a variable's bytes, zero past its length. -/
def view (var : Var) : List (State → Expr) :=
  (List.range ((var.length + 31) / 32)).map fun index state =>
    let value := state.load var.object (var.start + 32 * index)
    let kept := var.length - 32 * index
    if kept < 32 then band value (num (high kept)) else value

/-- The Word at byte `offset` of Words bound at `positions`. -/
private def loadFrom (state : State) (positions : List Nat) (offset : Nat) : Expr :=
  let wordOf := fun (index : Nat) => match positions[index]? with
    | some position => state.ref position
    | none => num 0
  let index := offset / 32
  let delta := offset % 32
  if delta = 0 then wordOf index
  else if index + 1 < positions.length then
    bor (shl (wordOf index) (num (8 * delta))) (shr (wordOf (index + 1)) (num (8 * (32 - delta))))
  else shl (wordOf index) (num (8 * delta))

/-- The bound Words and the length of a part. -/
def part (state : State) : Part → State × (List Nat × Nat)
  | .word operand =>
      let (state, position) := state.bind (state.operand operand)
      (state, ([position], 32))
  | .zeros count => (state, ([], count))
  | .value ref =>
      match state.scope.var? ref with
      | some var =>
          let (state, positions) := state.bindAll (view var)
          (state, (positions, var.length))
      | none => (state, ([], 0))

/-- The Words of the parts' bytes one after another, zero past their total
length. -/
def concatenation (parts : List (List Nat × Nat)) : List (State → Expr) :=
  let total := (parts.map (·.2)).sum
  (List.range ((total + 31) / 32)).map fun index state => Id.run do
    let mut word : Option Expr := none
    let mut offset := 0
    for (positions, length) in parts do
      let first := max (32 * index) offset
      let last := min (32 * index + 32) (offset + length)
      if first < last && !positions.isEmpty then
        let loaded := loadFrom state positions (first - offset)
        let placed := if first = 32 * index then loaded else shr loaded (num (8 * (first - 32 * index)))
        word := some (match word with
          | some previous => bor previous placed
          | none => placed)
      offset := offset + length
    return word.getD (num 0)

def setValue (state : State) (object : Nat) (positions : List Nat) : State :=
  {state with values := if object < state.values.size then state.values.set! object positions
                        else state.values ++ (Array.replicate (object - state.values.size) []).push positions}

/-- Select among bound Words by a Word key; past the last, zero. -/
def select (state : State) (positions : List Nat) (key : Expr) : Expr :=
  positions.zipIdx.foldr (fun (position, index) rest => .ifE (eq key (num index)) (state.ref position) rest) (num 0)

/-- Fail when `index` is not below `valid`; return the bound index. -/
def checked (state : State) (index : Expr) (valid : Nat) (failure : Failure) : State × Nat :=
  let (state, position) := state.bind index
  (state.fail (gt (state.ref position) (num (valid - 1))) failure, position)

/-- An observation's Word. -/
def access (state : State) (var : Var) : Access → State × Expr
  | .length => (state, num var.length)
  | .word (.literal value) => (state, state.load var.object (var.start + value))
  | .byte (.literal value) =>
      let offset := var.start + value
      (state, .binary .wordByte (num (offset % 32)) (state.wordAt var.object (offset / 32)))
  | .word index =>
      let (state, checkedIndex) := state.checked (state.index index) (var.length - 31) .bytes
      let (state, offset) := state.bind (add (state.ref checkedIndex) (num var.start))
      let (state, word) := state.bind (shr (state.ref offset) (num 5))
      let (state, bits) := state.bind (shl (band (state.ref offset) (num 31)) (num 3))
      let positions := state.wordsOf var.object
      let (state, next) := state.bind (add (state.ref word) (num 1))
      (state, bor (shl (state.select positions (state.ref word)) (state.ref bits))
        (shr (state.select positions (state.ref next)) (sub (num 256) (state.ref bits))))
  | .byte index =>
      let (state, checkedIndex) := state.checked (state.index index) var.length .bytes
      let (state, offset) := state.bind (add (state.ref checkedIndex) (num var.start))
      (state, .binary .wordByte (band (state.ref offset) (num 31))
        (state.select (state.wordsOf var.object) (shr (state.ref offset) (num 5))))
  | .hash =>
      let (state, positions) := state.bindAll (view var)
      let padded := positions.map state.ref ++ List.replicate (4 - positions.length) (num 0)
      match state.hash with
      | some closure => (state, .apply (state.ref closure) (packet (num var.length :: padded)))
      | none => (state, num 0)
  | .element (.literal value) _ => (state, state.wordAt var.object value)
  | .element index _ =>
      let (state, checkedIndex) := state.checked (state.index index) var.length .array
      (state, state.select (state.wordsOf var.object) (state.ref checkedIndex))

/-- Rebind the Words of a value after a write. -/
def write (state : State) (target : Ref) (var : Var) (index : Index) (value : Expr) (width : Width) : State :=
  let positions := state.wordsOf var.object
  let (state, written) := state.bind value
  if target.isArray then
    match index with
    | .literal element =>
        let (state, rebound) := state.bind (state.ref written)
        state.setValue var.object (positions.set element rebound)
    | _ =>
        let (state, checkedIndex) := state.checked (state.index index) var.length .array
        let (state, rebound) := state.bindAll (positions.zipIdx.map fun (position, element) state =>
          .ifE (eq (state.ref checkedIndex) (num element)) (state.ref written) (state.ref position))
        state.setValue var.object rebound
  else
    match width, index with
    | .word, .literal offset =>
        let offset := var.start + offset
        let word := offset / 32
        let delta := offset % 32
        if delta = 0 then
          let (state, rebound) := state.bind (state.ref written)
          state.setValue var.object (positions.set word rebound)
        else
          let (state, first) := state.bind (bor (band (state.wordAt var.object word) (num (high delta)))
            (shr (state.ref written) (num (8 * delta))))
          let (state, second) := state.bind (bor (band (state.wordAt var.object (word + 1)) (num (2 ^ (8 * (32 - delta)) - 1)))
            (shl (state.ref written) (num (8 * (32 - delta)))))
          state.setValue var.object ((positions.set word first).set (word + 1) second)
    | .byte, .literal offset =>
        let offset := var.start + offset
        let bits := 8 * (31 - offset % 32)
        let (state, rebound) := state.bind (bor (band (state.wordAt var.object (offset / 32)) (num (maximumWord - 255 * 2 ^ bits)))
          (shl (band (state.ref written) (num 255)) (num bits)))
        state.setValue var.object (positions.set (offset / 32) rebound)
    | .word, _ =>
        let (state, checkedIndex) := state.checked (state.index index) (var.length - 31) .bytes
        let (state, offset) := state.bind (add (state.ref checkedIndex) (num var.start))
        let (state, word) := state.bind (shr (state.ref offset) (num 5))
        let (state, bits) := state.bind (shl (band (state.ref offset) (num 31)) (num 3))
        let (state, rebound) := state.bindAll (positions.zipIdx.map fun (position, index) state =>
          .ifE (eq (state.ref word) (num index))
            (bor (band (state.ref position) (bnot (shr (num maximumWord) (state.ref bits))))
              (shr (state.ref written) (state.ref bits)))
            (.ifE (eq (add (state.ref word) (num 1)) (num index))
              (bor (band (state.ref position) (shr (num maximumWord) (state.ref bits)))
                (shl (state.ref written) (sub (num 256) (state.ref bits))))
              (state.ref position)))
        state.setValue var.object rebound
    | .byte, _ =>
        let (state, checkedIndex) := state.checked (state.index index) var.length .bytes
        let (state, offset) := state.bind (add (state.ref checkedIndex) (num var.start))
        let (state, word) := state.bind (shr (state.ref offset) (num 5))
        let (state, bits) := state.bind (sub (num 248) (shl (band (state.ref offset) (num 31)) (num 3)))
        let (state, rebound) := state.bindAll (positions.zipIdx.map fun (position, index) state =>
          .ifE (eq (state.ref word) (num index))
            (bor (band (state.ref position) (bnot (shl (num 255) (state.ref bits))))
              (shl (band (state.ref written) (num 255)) (state.ref bits)))
            (state.ref position))
        state.setValue var.object rebound

/-- One action: its Core, then the static scope's step. -/
def action (state : State) (inLoop : Bool) (action : Action) : State :=
  let scope := (state.scope.step? inLoop action).getD state.scope
  match action with
  | .bytes build =>
      let parts := match build with
        | .toBytes part => [part]
        | .concat left right => [left, right]
      let (state, bound) := parts.foldl (fun (state, bound) part =>
        let (state, value) := state.part part
        (state, bound ++ [value])) (state, [])
      let (state, positions) := state.bindAll (concatenation bound)
      {state.setValue state.scope.objects.length positions with scope}
  | .array _ elements =>
      let (state, positions) := state.bindAll (elements.map fun element state => state.operand element)
      {state.setValue state.scope.objects.length positions with scope}
  | .slice .. | .alias _ => {state with scope}
  | .write target index value width _ =>
      match state.scope.var? target with
      | some var => {state.write target var index (state.operand value) width with scope}
      | none => {state with scope}
  | .observe fold constant value access =>
      match state.scope.var? value with
      | some var =>
          let (state, observed) := state.access var access
          let scaled := mul (state.ref state.acc) (num constant)
          let (state, acc) := state.bind (match fold with
            | .add => add scaled observed
            | .xor => bxor scaled observed)
          {state with acc, scope}
      | none => {state with scope}

/-- Values written in a loop body that exist before it, in creation order. -/
def written (state : State) (body : List Action) : List Nat := Id.run do
  let mut scope := state.scope
  let mut objects : List Nat := []
  for action in body do
    if let .write target .. := action then
      if let some var := scope.var? target then
        if var.object < state.scope.objects.length && !objects.contains var.object then
          objects := objects ++ [var.object]
    scope := (scope.step? true action).getD scope
  return objects.mergeSort (· ≤ ·)

/-- The loop's state: the accumulator, then the Words of every written value. -/
def components (state : State) (objects : List Nat) : List Nat :=
  state.acc :: objects.flatMap state.wordsOf

/-- Rebind the accumulator and the written values from bound components. -/
def restore (state : State) (objects : List Nat) (positions : List Nat) : State := Id.run do
  let mut state := {state with acc := positions.headD state.acc}
  let mut rest := positions.drop 1
  for object in objects do
    let count := (state.wordsOf object).length
    state := state.setValue object (rest.take count)
    rest := rest.drop count
  return state

/-- Bind the components of the state at `source`. -/
def unpackState (state : State) (count : Nat) (source : Nat) : State × List Nat :=
  state.bindAll ((List.range count).map fun index state => field index count (state.ref source))

/-- `fun (counter, state) => body`: the body's Core over the components,
returning the left injection of the new state or, out of range, the right
one of the failure's code. `enter` binds the loop's position from the
counter. -/
def iteration (state : State) (objects : List Nat) (enter : State → Nat → State × Nat)
    (body : State → State) : State × Nat :=
  let count := (state.components objects).length
  let stateType := words count
  let outer := state.builder
  let parameter := outer.size
  let inner : State := {state with builder := {size := outer.size + 1}, left := stateType}
  let (inner, position) := enter inner parameter
  let (inner, source) := inner.bind (.second (inner.ref parameter))
  let (inner, positions) := inner.unpackState count source
  let inner := body {inner.restore objects positions with counter := some position}
  let result := Expr.inLeft .word (packet ((inner.components objects).map inner.ref))
  let lambda := Expr.lambda (.product .word stateType) (.sum stateType .word) (inner.builder.close result inner.left)
  {state with builder := outer, scope := inner.scope}.bind lambda

/-- `st_{k+1} = case st_k of inl s => if limit > k then closure (k, s) else
inl s | inr c => inr c` for every ordinal below `trips`. -/
def chain (state : State) (stateType : Ty) (limit closure start trips : Nat) : State × Nat := Id.run do
  let mut state := state
  let mut current := start
  for ordinal in List.range trips do
    let under := fun (position : Nat) => Expr.var (state.builder.size - position)
    let (next, position) := state.bind (.caseE (state.ref current)
      (.ifE (gt (under limit) (num ordinal)) (.apply (under closure) (.pair (num ordinal) (.var 0))) (.inLeft .word (.var 0)))
      (.inRight stateType (.var 0)))
    state := next
    current := position
  return (state, current)

/-- The outer closure of a nested loop: it binds `i` and the inner bound,
then the inner closure over `j`, whose position is `i + j`, and chains it
over its own state. -/
def nestedIteration (state : State) (objects : List Nat) (bound : Bound) (innerMask : Nat)
    (body : State → State) : State × Nat :=
  let count := (state.components objects).length
  let stateType := words count
  let outer := state.builder
  let parameter := outer.size
  let inner : State := {state with builder := {size := outer.size + 1}, left := stateType}
  let (inner, outerCounter) := inner.bind (.first (inner.ref parameter))
  let (inner, innerLimit) := inner.bind (band (match bound with
    | .input => inner.ref inner.input
    | .counter => add (inner.ref outerCounter) (num 1)) (num innerMask))
  let (inner, innerClosure) := inner.iteration objects
    (fun deepest innerParameter =>
      let (deepest, innerCounter) := deepest.bind (.first (deepest.ref innerParameter))
      deepest.bind (add (deepest.ref outerCounter) (deepest.ref innerCounter)))
    body
  let (inner, start) := inner.bind (.inLeft .word (.second (inner.ref parameter)))
  let (inner, final) := inner.chain stateType innerLimit innerClosure start innerMask
  let lambda := Expr.lambda (.product .word stateType) (.sum stateType .word)
    (inner.builder.close (inner.ref final) inner.left)
  {state with builder := outer, scope := inner.scope}.bind lambda

/-- A loop: its limit, its closure and chain from the left injection of the
current state, then the case that continues with the final state's
components or aborts. -/
def loop (state : State) (loop : Loop) (body : List Action) : State :=
  let objects := state.written body
  let initial := state.components objects
  let count := initial.length
  let stateType := words count
  let outerScope := state.scope
  let compileBody := fun (inner : State) => body.foldl (fun inner action => inner.action true action) inner
  let (state, closure, trips, limit) := match loop with
    | .single mask =>
        let (state, limit) := state.bind (band (state.ref state.input) (num mask))
        let (state, closure) := state.iteration objects
          (fun inner parameter => inner.bind (.first (inner.ref parameter))) compileBody
        (state, closure, mask, limit)
    | .nested outerMask bound innerMask =>
        let (state, limit) := state.bind (band (state.ref state.input) (num outerMask))
        let (state, closure) := state.nestedIteration objects bound innerMask compileBody
        (state, closure, outerMask, limit)
  let (state, start) := state.bind (.inLeft .word (packet (initial.map state.ref)))
  let (state, final) := state.chain stateType limit closure start trips
  let (state, payload) := state.unpack (state.ref final)
  let (state, positions) := state.unpackState count payload
  let state := state.restore objects positions
  let scope := state.scope.close outerScope
  let values := state.values ++ Array.replicate (scope.objects.length - state.values.size) []
  {state with scope, values, counter := none}

def step (state : State) : Step → State
  | .action action => state.action false action
  | .loop loop body => state.loop loop body

end State

namespace Plan

/-- `fun input => …`: the hash closure when the plan hashes, the
accumulator's zero, every step, then the left injection of the accumulator. -/
def expression (plan : Plan) : Expr :=
  let state : State := {builder := {size := 1}, input := 0}
  let state := if plan.hashes then
      let (state, closure) := state.bind hashClosure
      {state with hash := some closure}
    else state
  let (state, acc) := state.bind (num 0)
  let state := plan.steps.foldl State.step {state with acc}
  .lambda .word (.sum .word .word) (state.builder.close (.inLeft .word (state.ref state.acc)) state.left)

/-- The accumulator, or an out-of-range access's failure code. -/
def resultType : Ty := .sum .word .word

def program (plan : Plan) : Program := {
  resultType := .function .word resultType, dataDefinitions := [], body := plan.expression}

def applied (plan : Plan) (input : Word) : Program := {
  resultType, dataDefinitions := [], body := .apply plan.expression (.word input)}

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

/-- The nodes the budget bounds: the applied reference without the hash
closure. -/
def budgetNodes (plan : Plan) : Nat := plan.nodes - (if plan.hashes then hashNodes else 0)

end Plan

/-! Specified shapes, from the plan. -/

def Ref.kind : Ref → String
  | .bytes _ => "bytes"
  | .slice _ => "slice"
  | .array _ => "array"

def Index.kind : Index → String
  | .literal _ => "literal"
  | .input .. => "input"
  | .counter .. => "counter"

def Part.kind : Part → String
  | .word _ => "word"
  | .zeros _ => "zeros"
  | .value ref => ref.kind

def Cut.name : Cut → String
  | .drop _ => "drop"
  | .take _ => "take"
  | .window .. => "window"

def Width.name : Width → String
  | .word => "word"
  | .byte => "byte"

def Form.name : Form → String
  | .inline => "inline"
  | .helper => "helper"

def Loop.shape : Loop → String
  | .single mask => "single:" ++ toString mask
  | .nested _ .input _ => "nested:input"
  | .nested _ .counter _ => "nested:counter"

def Action.kind : Action → String
  | .bytes _ => "bytes"
  | .slice .. => "slice"
  | .alias _ => "alias"
  | .array .. => "array"
  | .write .. => "write"
  | .observe .. => "observe"

/-- The length class of a hashed value. -/
def hashClass (length : Nat) : String :=
  if length = 0 then "0" else if length < 32 then "1-31" else if length = 32 then "32"
  else if length < 64 then "33-63" else if length = 64 then "64" else if length < 96 then "65-95"
  else if length = 96 then "96" else if length < 128 then "97-127" else "128"

/-- What an action adds to every dimension but `loops` and `body`, given the
writes and copies before it: `(value, variable, helper)` and
`(copy, source, writes to the source so far)`. -/
structure Trace where
  shapes : List (String × String) := []
  writes : List (Nat × Ref × Bool) := []
  copies : List (Nat × Nat × Nat) := []

def Trace.add (trace : Trace) (dimension value : String) : Trace :=
  {trace with shapes := trace.shapes ++ [(dimension, value)]}

def Trace.action (trace : Trace) (scope : Scope) : Action → Trace
  | .bytes build =>
      let (form, parts) := match build with
        | .toBytes part => ("to_bytes", [part])
        | .concat left right => ("concat", [left, right])
      let trace := parts.foldl (fun trace part => trace.add "parts" (form ++ ":" ++ part.kind)) (trace.add "values" "bytes")
      let object := scope.objects.length
      let sources := parts.filterMap fun part => match part with
        | .value ref => (scope.var? ref).map (·.object)
        | _ => none
      {trace with copies := trace.copies ++ sources.map fun source =>
        (object, source, (trace.writes.filter (·.1 == source)).length)}
  | .slice source cut => (trace.add "values" "slice").add "cuts" (cut.name ++ ":" ++ source.kind)
  | .alias source => trace.add "values" ("alias:" ++ source.kind)
  | .array allocated _ => trace.add "values" (if allocated then "array:allocated" else "array:literal")
  | .write target index _ width form =>
      let shape := if target.isArray then "array:" ++ form.name
        else target.kind ++ ":" ++ width.name ++ ":" ++ form.name
      let access := if target.isArray then "set" else match width with
        | .word => "put"
        | .byte => "put8"
      let trace := (trace.add "writes" shape).add "indices" (access ++ ":" ++ index.kind)
      match scope.var? target with
      | some var => {trace with writes := trace.writes ++ [(var.object, target, form == .helper)]}
      | none => trace
  | .observe _ _ value access =>
      let trace := match access with
        | .length => trace.add "observations" ("length:" ++ value.kind)
        | .word index => (trace.add "observations" ("word:" ++ value.kind)).add "indices" ("word:" ++ index.kind)
        | .byte index => (trace.add "observations" ("byte:" ++ value.kind)).add "indices" ("byte:" ++ index.kind)
        | .hash => trace.add "observations" ("hash:" ++ value.kind)
        | .element index get =>
            (trace.add "observations" (if get then "element:get" else "element:index")).add "indices" ("element:" ++ index.kind)
      match scope.var? value with
      | none => trace
      | some var =>
          let trace := if access == .hash then trace.add "hashes" (hashClass var.length) else trace
          let earlier := trace.writes.filter (·.1 == var.object)
          let trace := earlier.foldl (fun trace (_, writer, helper) =>
            let trace := if writer != value then
                trace.add "hazards" (if writer.isSlice || value.isSlice then "view" else "alias")
              else trace
            if helper then trace.add "hazards" "helper" else trace) trace
          let copied := trace.copies.any fun (copy, source, before) =>
            copy == var.object && (trace.writes.filter (·.1 == source)).length > before
          if copied then trace.add "hazards" "copy" else trace

def Plan.shapes (plan : Plan) : List (String × List String) := Id.run do
  let mut scope : Scope := {}
  let mut trace : Trace := {}
  let mut loops : List String := []
  let mut body : List String := []
  for step in plan.steps do
    match step with
    | .action action =>
        trace := trace.action scope action
        scope := (scope.step? false action).getD scope
    | .loop shape actions =>
        loops := loops ++ [shape.shape]
        let mut inner := scope
        for action in actions do
          body := body ++ [action.kind]
          trace := trace.action inner action
          inner := (inner.step? true action).getD inner
        scope := inner.close scope
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let of := fun (dimension : String) => sorted (trace.shapes.filterMap fun (name, value) =>
    if name == dimension then some value else none)
  return [("values", of "values"), ("parts", of "parts"), ("cuts", of "cuts"), ("writes", of "writes"),
    ("observations", of "observations"), ("indices", of "indices"), ("hazards", of "hazards"),
    ("loops", if loops.isEmpty then ["none"] else sorted loops), ("body", sorted body), ("hashes", of "hashes")]

/-! Generation. -/

def domain : UInt64 := 0x6d656d76616c0001

private def pick {α : Type} [Inhabited α] (values : List α) : Gen α := do
  return values[← draw values.length]!

def drawOperand (inLoop : Bool) : Gen Operand := do
  match ← drawWeighted [3, 1, 1, 1, 1, if inLoop then 3 else 0] with
  | 0 => return .input
  | 1 => return .add (1 + (← draw 255))
  | 2 => return .mul (2 + (← draw 254))
  | 3 => return .xor (1 + (← draw 255))
  | 4 => return .acc
  | _ => return .counter

def drawIndex (inLoop : Bool) (valid : Nat) : Gen Index := do
  match ← drawWeighted [2, 3, if inLoop then 3 else 0] with
  | 0 => return .literal (← draw valid)
  | 1 => return .input (← pick shifts) (1 + (← draw (valid + indexSlack)))
  | _ => return .counter (← pick scales) (← draw (maximumOffset + 1))

def drawZeros : Gen Nat := do
  match ← draw 4 with
  | 0 => return 0
  | 1 => return 1 + (← draw 31)
  | 2 => return 32
  | _ => return 33 + (← draw 8)

/-- Bytes values and slices in scope. -/
def Scope.sources (scope : Scope) : List Ref := scope.visible.filter (!·.isArray)

/-- The longest bytes value or slice in scope, the first of equals. -/
def Scope.longest (scope : Scope) : Option Ref :=
  scope.sources.foldl (fun best ref => match best with
    | none => some ref
    | some current =>
        if ((scope.var? ref).map (·.length)).getD 0 > ((scope.var? current).map (·.length)).getD 0 then some ref
        else best) none

/-- A part; a copy (`to_bytes` of one part) favours a value. A value part is
the longest in scope half the time. -/
def drawPart (scope : Scope) (inLoop : Bool) (copy : Bool := false) : Gen Part := do
  let sources := scope.sources
  match ← drawWeighted [if copy then 1 else 3, if copy then 1 else 2, if sources.isEmpty then 0 else 4] with
  | 0 => return .word (← drawOperand inLoop)
  | 1 => return .zeros (← drawZeros)
  | _ =>
      if (← draw 2) = 0 then
        if let some longest := scope.longest then return .value longest
      return .value (← pick sources)

/-- Slices in scope. -/
def Scope.cuts (scope : Scope) : List Ref := scope.visible.filter (·.isSlice)

/-- A copy is of a slice half the time when one is in scope; a concatenation
over 128 bytes keeps its left part. -/
def drawBuild (scope : Scope) (inLoop : Bool) : Gen Build := do
  if (← draw 3) = 0 then
    if !scope.cuts.isEmpty && (← draw 2) = 0 then return .toBytes (.value (← pick scope.cuts))
    return .toBytes (← drawPart scope inLoop true)
  let left ← drawPart scope inLoop
  let right ← drawPart scope inLoop
  match Scope.buildLength? scope inLoop (.concat left right) with
  | some length => return if length ≤ maximumLength then .concat left right else .toBytes left
  | none => return .toBytes left

/-- Cuts keep at least half of a value, a window at least half of what its
start leaves. -/
def drawCut (length : Nat) : Gen Cut := do
  match ← draw 3 with
  | 0 => return .drop (← draw (length / 2 + 1))
  | 1 => return .take (length - (← draw (length / 2 + 1)))
  | _ =>
      let start ← draw (length / 4 + 1)
      return .window start (length - start - (← draw ((length - start) / 2 + 1)))

def drawAccess (inLoop : Bool) (ref : Ref) (var : Var) (hash : Bool) : Gen Access := do
  if ref.isArray then return .element (← drawIndex inLoop var.length) ((← draw 2) = 1)
  match ← drawWeighted [1, if 32 ≤ var.length then 3 else 0, if 1 ≤ var.length then 2 else 0, if hash then 3 else 0] with
  | 0 => return .length
  | 1 => return .word (← drawIndex inLoop (var.length - 31))
  | 2 => return .byte (← drawIndex inLoop var.length)
  | _ => return .hash

/-- The observed variable: the longest bytes value or slice a quarter of the
time, otherwise any in scope. -/
def drawObserve (scope : Scope) (inLoop : Bool) (hash : Bool) : Gen Action := do
  let longest := if (← draw 4) = 0 then scope.longest else none
  let value ← match longest with
    | some ref => pure ref
    | none => pick scope.visible
  let var := (scope.var? value).getD default
  let fold := if (← draw 2) = 0 then Fold.add else .xor
  return .observe fold (← pick foldConstants) value (← drawAccess inLoop value var hash)

def Scope.targets (scope : Scope) : List Ref :=
  scope.visible.filter fun ref => match scope.var? ref with
    | some var => ref.isArray || 1 ≤ var.length
    | none => false

def drawWrite (scope : Scope) (inLoop : Bool) : Gen Action := do
  let target ← pick scope.targets
  let var := (scope.var? target).getD default
  let width ← if target.isArray then pure Width.word
    else if 32 ≤ var.length && (← draw 2) = 0 then pure Width.word else pure Width.byte
  let valid := if target.isArray then var.length else (width.valid? var.length).getD 1
  let index ← drawIndex inLoop valid
  let value ← drawOperand inLoop
  let form := if (← draw 2) = 0 then Form.inline else .helper
  return .write target index value width form

def Scope.aliases (scope : Scope) : List Ref :=
  scope.visible.filter fun ref => match ref with
    | .bytes _ => scope.bytes.length < maximumBytes
    | .array _ => scope.arrays.length < maximumArrays
    | .slice _ => false

/-- One action the scope admits, or `none` when none is possible. -/
def drawAction (scope : Scope) (inLoop : Bool) (hash : Bool) : Gen (Option Action) := do
  let visible := !scope.visible.isEmpty
  let weights := [
    if scope.bytes.length < maximumBytes then (if inLoop then 1 else 3) else 0,
    if scope.slices.length < maximumSlices && !scope.sources.isEmpty then (if inLoop then 1 else 3) else 0,
    if !inLoop && !scope.aliases.isEmpty then 1 else 0,
    if scope.arrays.length < maximumArrays then (if inLoop then 1 else 2) else 0,
    if !scope.targets.isEmpty then 3 else 0,
    if visible then (if inLoop then 4 else 5) else 0]
  if weights.sum = 0 then return none
  match ← drawWeighted weights with
  | 0 => return some (.bytes (← drawBuild scope inLoop))
  | 1 =>
      let source ← pick scope.sources
      return some (.slice source (← drawCut ((scope.var? source).getD default).length))
  | 2 => return some (.alias (← pick scope.aliases))
  | 3 =>
      let count := 1 + (← draw maximumElements)
      let mut elements : List Operand := []
      for _ in List.range count do
        elements := elements ++ [← drawOperand inLoop]
      return some (.array ((← draw 2) = 1) elements)
  | 4 => return some (← drawWrite scope inLoop)
  | _ => return some (← drawObserve scope inLoop hash)

def drawLoop : Gen Loop := do
  if (← draw 5) < 3 then return .single (← pick singleMasks)
  let outer ← pick nestedMasks
  let bound := if (← draw 2) = 0 then Bound.input else .counter
  return .nested outer bound (← pick nestedMasks)

/-- One to eight steps, half the plans with one loop of one to three actions;
when no step observes, a Word's bytes if nothing is in scope, then an
observation. -/
def drawPlan : Gen Plan := do
  let count := 1 + (← draw (maximumSteps - 2))
  let mut loopAt : Option Nat := none
  if (← draw 2) = 1 then loopAt := some (← draw count)
  let mut scope : Scope := {}
  let mut steps : List Step := []
  let mut hashes := 0
  for position in List.range count do
    if loopAt == some position then
      let shape ← drawLoop
      let bodyCount := 1 + (← draw maximumBody)
      let mut inner := scope
      let mut body : List Action := []
      for _ in List.range bodyCount do
        if let some action ← drawAction inner true (hashes + shape.trips ≤ maximumHashes) then
          if action.hashes then hashes := hashes + shape.trips
          body := body ++ [action]
          inner := (inner.step? true action).getD inner
      unless body.isEmpty do
        steps := steps ++ [.loop shape body]
        scope := inner.close scope
    else
      if let some action ← drawAction scope false (hashes + 1 ≤ maximumHashes) then
        if action.hashes then hashes := hashes + 1
        steps := steps ++ [.action action]
        scope := (scope.step? false action).getD scope
  unless steps.any (fun step => step.actions.any (·.observes)) do
    if scope.visible.isEmpty then
      let action := Action.bytes (.toBytes (.word .input))
      steps := steps ++ [.action action]
      scope := (scope.step? false action).getD scope
    steps := steps ++ [.action (← drawObserve scope false (hashes + 1 ≤ maximumHashes))]
  return {steps}

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- Steps are dropped from the end while the budgeted reference exceeds
`nodes`, more than one step remains and the rest still observes. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.steps.length do
    let shorter : Plan := {steps := plan.steps.dropLast}
    if plan.budgetNodes > nodes && plan.steps.length > 1 && shorter.admitted then
      plan := shorter
  return plan

end Solcore.Synthesis.Core.MemoryValues
end

section
-- leanmerge: from Solcore.Synthesis.Core.MemoryValuesShrink
/-! Reductions of memory value plans. A candidate is kept only when the plan
is admitted and strictly smaller: in its structure first, then in the sum of
its numeric literals. Removing a declaration renumbers the later variables of
its kind; a candidate that would still refer to it is not formed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryValues

def Operand.size : Operand → Nat × Nat
  | .input => (1, 0)
  | .add constant | .mul constant | .xor constant => (2, constant)
  | .acc | .counter => (2, 0)

def Index.size : Index → Nat × Nat
  | .literal value => (1, value)
  | .input shift modulus => (2, shift + modulus)
  | .counter scale offset => (2, scale + offset)

private def plus (left right : Nat × Nat) : Nat × Nat := (left.1 + right.1, left.2 + right.2)

private def sumOf {α : Type} (size : α → Nat × Nat) (values : List α) : Nat × Nat :=
  values.foldl (fun total value => plus total (size value)) (0, 0)

def Part.size : Part → Nat × Nat
  | .word operand => plus (1, 0) operand.size
  | .zeros count => (1, count)
  | .value _ => (1, 0)

def Build.size : Build → Nat × Nat
  | .toBytes part => plus (1, 0) part.size
  | .concat left right => plus (2, 0) (plus left.size right.size)

def Cut.size : Cut → Nat × Nat
  | .drop start => (1, start)
  | .take kept => (1, kept)
  | .window start kept => (2, start + kept)

def Access.size : Access → Nat × Nat
  | .length => (1, 0)
  | .word index | .byte index => plus (2, 0) index.size
  | .hash => (2, 0)
  | .element index get => plus (if get then 3 else 2, 0) index.size

def Action.size : Action → Nat × Nat
  | .bytes build => plus (1, 0) build.size
  | .slice _ cut => plus (1, 0) cut.size
  | .alias _ => (1, 0)
  | .array allocated elements => plus (if allocated then 2 else 1, 0) (sumOf Operand.size elements)
  | .write _ index value _ form => plus (if form == .helper then 2 else 1, 0) (plus index.size value.size)
  | .observe fold constant _ access => plus (if fold == .xor then 2 else 1, constant) access.size

def Loop.size : Loop → Nat × Nat
  | .single mask => (1, mask)
  | .nested outer _ inner => (3, outer + inner)

def Step.size : Step → Nat × Nat
  | .action single => plus (1, 0) single.size
  | .loop shape body => plus (1, 0) (plus shape.size (sumOf (fun single => plus (1, 0) single.size) body))

/-- Structure first, then literals; literals stay far below `2 ^ 16`. -/
def Plan.size (plan : Plan) : Nat :=
  let (shape, literals) := sumOf Step.size plan.steps
  shape * 2 ^ 16 + literals

/-! Renumbering after a removed declaration. -/

/-- The declarations an action makes, by kind. -/
def Action.declares (scope : Scope) : Action → Option String
  | .bytes _ => some "bytes"
  | .slice .. => some "slice"
  | .alias source => if source.isArray then some "array" else some "bytes"
  | .array .. => some "array"
  | _ => let _ := scope; none

/-- Map a variable after the declarations `[first, first + count)` of a kind
are removed; `none` when it is one of them. -/
def Ref.renumber (kind : String) (first count : Nat) (ref : Ref) : Option Ref :=
  if ref.kind != kind || ref.number < first then some ref
  else if ref.number < first + count then none
  else some (match ref with
    | .bytes number => .bytes (number - count)
    | .slice number => .slice (number - count)
    | .array number => .array (number - count))

def Part.renumber (kind : String) (first count : Nat) : Part → Option Part
  | .value ref => (ref.renumber kind first count).map .value
  | part => some part

def Action.renumber (kind : String) (first count : Nat) : Action → Option Action
  | .bytes (.toBytes part) => do return .bytes (.toBytes (← part.renumber kind first count))
  | .bytes (.concat left right) => do
      return .bytes (.concat (← left.renumber kind first count) (← right.renumber kind first count))
  | .slice source cut => do return .slice (← source.renumber kind first count) cut
  | .alias source => do return .alias (← source.renumber kind first count)
  | .write target index value width form => do
      return .write (← target.renumber kind first count) index value width form
  | .observe fold constant value access => do
      return .observe fold constant (← value.renumber kind first count) access
  | action => some action

def Step.renumber (kind : String) (first count : Nat) : Step → Option Step
  | .action single => (single.renumber kind first count).map .action
  | .loop shape body => do return .loop shape (← body.mapM (·.renumber kind first count))

/-- How many declarations of each kind the actions make. -/
def declarationCounts (actions : List Action) : List (String × Nat) :=
  ["bytes", "slice", "array"].map fun kind =>
    (kind, (actions.filter fun action => action.declares {} == some kind).length)

def Plan.declarationsBefore (plan : Plan) (index : Nat) : List (String × Nat) :=
  declarationCounts ((plan.steps.take index).flatMap (·.actions))

/-- Remove the actions `removed` from the plan at step `index`, renumbering
every later step, `rest` being the steps after them. -/
private def renumberRest (before : List (String × Nat)) (removed : List Action) (rest : List Step) : Option (List Step) :=
  (declarationCounts removed).foldlM (fun steps (kind, count) =>
    if count = 0 then some steps
    else steps.mapM (·.renumber kind ((before.lookup kind).getD 0) count)) rest

def Plan.removeStep (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let rest ← renumberRest (plan.declarationsBefore index) step.actions (plan.steps.drop (index + 1))
  return {steps := plan.steps.take index ++ rest}

/-- Remove action `position` of the loop at step `index`. -/
def Plan.removeBodyAction (plan : Plan) (index position : Nat) : Option Plan := do
  let .loop shape body ← plan.steps[index]? | none
  let action ← body[position]?
  let before := declarationCounts ((plan.steps.take index).flatMap (·.actions) ++ body.take position)
  let following ← renumberRest before [action] ((body.drop (position + 1)).map Step.action)
  let later ← renumberRest before [action] (plan.steps.drop (index + 1))
  let kept := body.take position ++ following.filterMap fun step => match step with
    | .action single => some single
    | .loop .. => none
  return {steps := plan.steps.take index ++ [.loop shape kept] ++ later}

/-! Local reductions of operands, indices, builds, cuts, arrays,
observations, writes and loops. -/

def Operand.reductions : Operand → List Operand
  | .input => []
  | _ => [.input]

def Index.reductions : Index → List Index
  | .literal 0 => []
  | _ => [.literal 0]

def Part.reductions : Part → List Part
  | .word operand => operand.reductions.map .word
  | .zeros count => if count = 0 then [] else [.zeros 0]
  | .value _ => []

def Build.reductions : Build → List Build
  | .toBytes part => part.reductions.map .toBytes
  | .concat left right =>
      [.toBytes left, .toBytes right] ++ left.reductions.map (.concat · right) ++
        right.reductions.map (.concat left ·)

def Cut.reductions : Cut → List Cut
  | .drop start => if start = 0 then [] else [.drop 0]
  | .take kept => if kept = 0 then [] else [.take 0]
  | .window start kept => [.drop start, .take kept]

def Access.reductions : Access → List Access
  | .length => []
  | .word index => .length :: index.reductions.map .word
  | .byte index => .length :: index.reductions.map .byte
  | .hash => [.length]
  | .element index get => (if get then [.element index false] else []) ++ index.reductions.map (.element · get)

private def replaceAt {α : Type} (values : List α) (index : Nat) (value : α) : List α :=
  values.set index value

def Action.reductions : Action → List Action
  | .bytes build => build.reductions.map .bytes
  | .slice source cut => cut.reductions.map (.slice source ·)
  | .alias _ => []
  | .array allocated elements =>
      (if allocated then [.array false elements] else []) ++
      (if elements.length > 1 then [.array allocated elements.dropLast] else []) ++
      elements.zipIdx.flatMap fun (element, index) =>
        element.reductions.map fun reduced => .array allocated (replaceAt elements index reduced)
  | .write target index value width form =>
      (if form == .helper then [.write target index value width .inline] else []) ++
      index.reductions.map (fun reduced => .write target reduced value width form) ++
      value.reductions.map (fun reduced => .write target index reduced width form)
  | .observe fold constant value access =>
      (if fold == .xor then [.observe .add constant value access] else []) ++
      (if constant > 3 then [.observe fold 3 value access] else []) ++
      access.reductions.map (.observe fold constant value ·)

def Loop.reductions : Loop → List Loop
  | .single 7 => [.single 3]
  | .single 3 => [.single 1]
  | .single _ => []
  | .nested outer bound inner =>
      [.single 1] ++ (if outer = 3 then [.nested 1 bound inner] else []) ++
        (if inner = 3 then [.nested outer bound 1] else []) ++
        (if bound == .counter then [.nested outer .input inner] else [])

def planReductions (plan : Plan) : List Plan := Id.run do
  let mut result : List Plan := []
  for index in List.range plan.steps.length do
    if let some reduced := plan.removeStep index then result := result ++ [reduced]
  for (step, index) in plan.steps.zipIdx do
    let replace := fun (step : Step) => ({steps := replaceAt plan.steps index step} : Plan)
    match step with
    | .action action =>
        result := result ++ action.reductions.map fun reduced => replace (.action reduced)
    | .loop shape body =>
        for position in List.range body.length do
          if body.length > 1 then
            if let some reduced := plan.removeBodyAction index position then result := result ++ [reduced]
        result := result ++ shape.reductions.map fun reduced => replace (.loop reduced body)
        for (action, position) in body.zipIdx do
          result := result ++ action.reductions.map fun reduced =>
            replace (.loop shape (replaceAt body position reduced))
  return result.filter fun candidate => candidate.admitted && candidate.size < plan.size

end Solcore.Synthesis.Core.MemoryValues
end

section
-- leanmerge: from Solcore.Synthesis.Source.MemoryValuesEmitter
/-! The Solcore source of a memory value plan: std's `memory<bytes>`,
`memory_ref` and `memory<DynArray<uint256>>` values in
`SynthesizedMemoryValues.run(uint256)`, with Word and byte reads through
std's range checks, writes inline or through helpers, and the bounded
`while` forms. The source is a function of the plan; nothing here builds or
reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryValues

open Solcore.Synthesis.Core.MemoryValues

def emitterVersion : String := "solcore-source-memory-values-v1"
def wrapperVersion : String := "solcore-word-memory-values-contract-v1"
def contractName : String := "SynthesizedMemoryValues"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedMemoryValuesDeploy"]
def runtimePath : List String := ["SynthesizedMemoryValuesDeploy", "SynthesizedMemoryValues"]

def refName : Ref → String
  | .bytes number => "sc_b" ++ toString number
  | .slice number => "sc_s" ++ toString number
  | .array number => "sc_a" ++ toString number

/-- The loop's position: `sc_counter`, or `(sc_i + sc_j)` in a nested loop. -/
def positionText : Loop → String
  | .single _ => "sc_counter"
  | .nested .. => "(sc_i + sc_j)"

def operandText (position : String) : Operand → String
  | .input => "sc_x"
  | .add constant => "(sc_x + " ++ toString constant ++ ")"
  | .mul constant => "(sc_x * " ++ toString constant ++ ")"
  | .xor constant => "(sc_x ^ " ++ toString constant ++ ")"
  | .acc => "sc_r"
  | .counter => position

def indexText (position : String) : Index → String
  | .literal value => toString value
  | .input shift modulus => "mod(shr(" ++ toString shift ++ ", sc_x), " ++ toString modulus ++ ")"
  | .counter scale offset =>
      let scaled := if scale = 1 then position else "(" ++ position ++ " * " ++ toString scale ++ ")"
      if offset = 0 then scaled else "(" ++ scaled ++ " + " ++ toString offset ++ ")"

def partText (position : String) : Part → String
  | .word operand => "bytes32(" ++ operandText position operand ++ ")"
  | .zeros count => "empty(" ++ toString count ++ ")"
  | .value ref => refName ref

def buildText (position : String) : Build → String
  | .toBytes part => "to_bytes(" ++ partText position part ++ ")"
  | .concat left right => "concat(" ++ partText position left ++ ", " ++ partText position right ++ ")"

def cutText (source : String) : Cut → String
  | .drop start => "slice_(" ++ source ++ ", " ++ toString start ++ ")"
  | .take kept => "truncate(" ++ source ++ ", " ++ toString kept ++ ")"
  | .window start kept => "truncate(slice_(" ++ source ++ ", " ++ toString start ++ "), " ++ toString kept ++ ")"

def accessText (position value : String) : Access → String
  | .length => "MemorySize.len(" ++ value ++ ")"
  | .word index => "sc_word(" ++ value ++ ", " ++ indexText position index ++ ")"
  | .byte index => "sc_byte(" ++ value ++ ", " ++ indexText position index ++ ")"
  | .hash => "Typedef.rep(keccak256_(" ++ value ++ "))"
  | .element index false => "Typedef.rep(" ++ value ++ "[uint256(" ++ indexText position index ++ ")])"
  | .element index true => "Typedef.rep(IndexAccess.get(" ++ value ++ ", uint256(" ++ indexText position index ++ ")))"

/-- Declaration numbers so far, by kind. -/
structure Names where
  bytes : Nat := 0
  slices : Nat := 0
  arrays : Nat := 0

private def arrayType : String := "memory<DynArray<uint256>>"

/-- An action's lines and the declaration numbers after it. -/
def actionLines (position : String) (names : Names) : Action → List String × Names
  | .bytes build =>
      (["let sc_b" ++ toString names.bytes ++ ": memory<bytes> = " ++ buildText position build ++ ";"],
       {names with bytes := names.bytes + 1})
  | .slice source cut =>
      (["let sc_s" ++ toString names.slices ++ ": memory_ref = " ++ cutText (refName source) cut ++ ";"],
       {names with slices := names.slices + 1})
  | .alias source =>
      match source with
      | .array _ =>
          (["let sc_a" ++ toString names.arrays ++ ": " ++ arrayType ++ " = " ++ refName source ++ ";"],
           {names with arrays := names.arrays + 1})
      | _ =>
          (["let sc_b" ++ toString names.bytes ++ ": memory<bytes> = " ++ refName source ++ ";"],
           {names with bytes := names.bytes + 1})
  | .array allocated elements =>
      let name := "sc_a" ++ toString names.arrays
      let lines := if allocated then
          ("let " ++ name ++ ": " ++ arrayType ++ " = allocateDynamicArray(@uint256, " ++ toString elements.length ++ ");") ::
          elements.zipIdx.map fun (element, index) =>
            "IndexAccess.set(" ++ name ++ ", uint256(" ++ toString index ++ "), uint256(" ++ operandText position element ++ "));"
        else
          ["let " ++ name ++ ": " ++ arrayType ++ " = [" ++
            ", ".intercalate (elements.map fun element => "uint256(" ++ operandText position element ++ ")") ++ "];"]
      (lines, {names with arrays := names.arrays + 1})
  | .write target index value width form =>
      let target := refName target |> fun name => (name, target.isArray)
      let index := indexText position index
      let value := operandText position value
      let line := match target.2, width, form with
        | true, _, .inline => "IndexAccess.set(" ++ target.1 ++ ", uint256(" ++ index ++ "), uint256(" ++ value ++ "));"
        | true, _, .helper => "sc_aput(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
        | false, .word, .inline => "mstore(MemoryPointer.ptr(truncate(slice_(" ++ target.1 ++ ", " ++ index ++ "), 32)), " ++ value ++ ");"
        | false, .byte, .inline => "mstore8(MemoryPointer.ptr(truncate(slice_(" ++ target.1 ++ ", " ++ index ++ "), 1)), " ++ value ++ ");"
        | false, .word, .helper => "sc_put(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
        | false, .byte, .helper => "sc_put8(" ++ target.1 ++ ", " ++ index ++ ", " ++ value ++ ");"
      ([line], names)
  | .observe fold constant value access =>
      let operator := match fold with
        | .add => " + "
        | .xor => " ^ "
      (["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ operator ++ accessText position (refName value) access ++ ");"], names)

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def bodyLines (position : String) (names : Names) (actions : List Action) : List String × Names :=
  actions.foldl (fun (lines, names) action =>
    let (more, names) := actionLines position names action
    (lines ++ more, names)) ([], names)

def loopLines (names : Names) (loop : Loop) (body : List Action) : List String × Names :=
  let position := positionText loop
  let (inner, names) := bodyLines position names body
  match loop with
  | .single mask =>
      (["let sc_limit: word = (sc_x & " ++ toString mask ++ ");",
        "let sc_counter: word = 0;",
        "while (sc_limit > sc_counter) {"] ++ indent 4 inner ++
       ["    sc_counter = (sc_counter + 1);", "}"], names)
  | .nested outer bound innerMask =>
      let innerBound := match bound with
        | .input => "(sc_x & " ++ toString innerMask ++ ")"
        | .counter => "((sc_i + 1) & " ++ toString innerMask ++ ")"
      (["let sc_outer: word = (sc_x & " ++ toString outer ++ ");",
        "let sc_i: word = 0;",
        "let sc_inner: word = 0;",
        "let sc_j: word = 0;",
        "while (sc_outer > sc_i) {",
        "    sc_inner = " ++ innerBound ++ ";",
        "    sc_j = 0;",
        "    while (sc_inner > sc_j) {"] ++ indent 8 inner ++
       ["        sc_j = (sc_j + 1);", "    }", "    sc_i = (sc_i + 1);", "}"], names)

/-- The helpers in emission order, each emitted when an action needs it. -/
def helperNames : List String := ["sc_word", "sc_byte", "sc_put", "sc_put8", "sc_aput"]

def actionHelpers : Action → List String
  | .observe _ _ _ (.word _) => ["sc_word"]
  | .observe _ _ _ (.byte _) => ["sc_byte"]
  | .write target _ _ width .helper =>
      if target.isArray then ["sc_aput"] else match width with
        | .word => ["sc_put"]
        | .byte => ["sc_put8"]
  | _ => []

def planHelpers (plan : Plan) : List String :=
  let used := plan.steps.flatMap fun step => step.actions.flatMap actionHelpers
  helperNames.filter used.contains

def helperLines : String → List String
  | "sc_word" => [
      "function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
      "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));", "}", ""]
  | "sc_byte" => [
      "function sc_byte<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
      "    return shr(248, mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1))));", "}", ""]
  | "sc_put" => [
      "function sc_put<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
      "    mstore(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)), sc_w);", "}", ""]
  | "sc_put8" => [
      "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
      "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);", "}", ""]
  | "sc_aput" => [
      "function sc_aput(sc_a: memory<DynArray<uint256>>, sc_i: word, sc_w: word) returns (()) {",
      "    IndexAccess.set(sc_a, uint256(sc_i), uint256(sc_w));", "}", ""]
  | _ => []

def emit (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    match step with
    | .action action =>
        let (more, next) := actionLines "sc_counter" names action
        lines := lines ++ more
        names := next
    | .loop loop body =>
        let (more, next) := loopLines names loop body
        lines := lines ++ more
        names := next
  let source := ["import * from std;", "import * from std.dispatch;",
      "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] ++
    (planHelpers plan).flatMap helperLines ++
    ["contract " ++ contractName ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.MemoryValues
end

section
-- leanmerge: from Solcore.Synthesis.Source.MemoryValuesCases
/-! A memory value case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference
models every value as its byte list, never std's layout, and is built from
the plan, never from the source. Its right injection is an out-of-range
access's failure code, observed as std's revert data: `OutOfBounds()` for a
value's Words and bytes and `Panic(0x32)` for an array element. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryValues
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.MemoryValues

def caseSchema : String := "solcore-lean.semantic-memory-value-case.v1"
def planSchema : String := "solcore-lean.memory-value-plan.v1"
def profileVersion : String := "runtime-memory-values-v1/plan-seed-v1"

/-- std's `OutOfBounds()` selector, the whole revert data of `slice_` and
`truncate` past a value's end. -/
def outOfBounds : String := "0xb4120f14"

/-- std's `Panic(0x32)`, the whole revert data of a memory array's element
access past its length, through `IndexAccess` or `a[i]`, since solcore-rs
`e2eef194`. -/
def arrayOutOfBounds : String := "0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ "32"

/-- The revert data of an out-of-range access's failure code. -/
def failureOutput? (code : Word) : Option String :=
  if code.val = Solcore.Synthesis.Core.MemoryValues.Failure.bytes.code then some outOfBounds
  else if code.val = Solcore.Synthesis.Core.MemoryValues.Failure.array.code then some arrayOutOfBounds
  else none

/-- The node budget, which bounds the applied reference without the hash
closure, and the decode bound of a saved reference: the largest budget and
the closure. -/
def defaultNodes : Nat := 1024
def minimumNodes : Nat := 256
def maximumNodes : Nat := 2048
def caseLimit : Nat := 5120

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan where private mk ::
  plan : Plan
  admitted : plan.admitted = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? (plan : Plan) : Option CheckedPlan :=
  if admitted : plan.admitted = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

/-! Plan JSON. Every decoder is strict and the decoded plan must re-encode to
the saved JSON. -/

def operandJson : Operand → Json
  | .input => Json.mkObj [("operand", toJson "input")]
  | .add constant => Json.mkObj [("operand", toJson "add"), ("constant", toJson constant)]
  | .mul constant => Json.mkObj [("operand", toJson "mul"), ("constant", toJson constant)]
  | .xor constant => Json.mkObj [("operand", toJson "xor"), ("constant", toJson constant)]
  | .acc => Json.mkObj [("operand", toJson "acc")]
  | .counter => Json.mkObj [("operand", toJson "counter")]

def indexJson : Index → Json
  | .literal value => Json.mkObj [("index", toJson "literal"), ("value", toJson value)]
  | .input shift modulus => Json.mkObj [("index", toJson "input"), ("shift", toJson shift), ("modulus", toJson modulus)]
  | .counter scale offset => Json.mkObj [("index", toJson "counter"), ("scale", toJson scale), ("offset", toJson offset)]

def refJson (ref : Ref) : Json := toJson (refName ref)

def partJson : Part → Json
  | .word operand => Json.mkObj [("part", toJson "word"), ("operand", operandJson operand)]
  | .zeros count => Json.mkObj [("part", toJson "zeros"), ("count", toJson count)]
  | .value ref => Json.mkObj [("part", toJson "value"), ("value", refJson ref)]

def accessJson : Access → Json
  | .length => Json.mkObj [("access", toJson "length")]
  | .word index => Json.mkObj [("access", toJson "word"), ("index", indexJson index)]
  | .byte index => Json.mkObj [("access", toJson "byte"), ("index", indexJson index)]
  | .hash => Json.mkObj [("access", toJson "hash")]
  | .element index get => Json.mkObj [("access", toJson "element"), ("index", indexJson index),
      ("form", toJson (if get then "get" else "index"))]

def actionJson : Action → Json
  | .bytes (.toBytes part) => Json.mkObj [("kind", toJson "bytes"), ("build", toJson "to_bytes"),
      ("parts", .arr #[partJson part])]
  | .bytes (.concat left right) => Json.mkObj [("kind", toJson "bytes"), ("build", toJson "concat"),
      ("parts", .arr #[partJson left, partJson right])]
  | .slice source cut =>
      let fields := match cut with
        | .drop start => [("cut", toJson "drop"), ("start", toJson start)]
        | .take kept => [("cut", toJson "take"), ("length", toJson kept)]
        | .window start kept => [("cut", toJson "window"), ("start", toJson start), ("length", toJson kept)]
      Json.mkObj ([("kind", toJson "slice"), ("source", refJson source)] ++ fields)
  | .alias source => Json.mkObj [("kind", toJson "alias"), ("source", refJson source)]
  | .array allocated elements => Json.mkObj [("kind", toJson "array"),
      ("form", toJson (if allocated then "allocated" else "literal")),
      ("elements", .arr (elements.map operandJson).toArray)]
  | .write target index value width form => Json.mkObj [("kind", toJson "write"), ("target", refJson target),
      ("index", indexJson index), ("value", operandJson value), ("width", toJson width.name), ("form", toJson form.name)]
  | .observe fold constant value access => Json.mkObj [("kind", toJson "observe"),
      ("fold", toJson (match fold with
        | .add => "add"
        | .xor => "xor")), ("constant", toJson constant), ("value", refJson value), ("access", accessJson access)]

def loopJson : MemoryValues.Loop → Json
  | .single mask => Json.mkObj [("form", toJson "single"), ("mask", toJson mask)]
  | .nested outer bound inner => Json.mkObj [("form", toJson "nested"), ("outer", toJson outer),
      ("bound", toJson (match bound with
        | .input => "input"
        | .counter => "counter")), ("inner", toJson inner)]

def stepJson : Step → Json
  | .action action => Json.mkObj [("action", actionJson action)]
  | .loop shape body => Json.mkObj [("loop", loopJson shape), ("body", .arr (body.map actionJson).toArray)]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("steps", .arr (plan.steps.map stepJson).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def operandOf (json : Json) : Except String Operand := do
  match ← json.getObjValAs? String "operand" with
  | "input" => return .input
  | "add" => return .add (← json.getObjValAs? Nat "constant")
  | "mul" => return .mul (← json.getObjValAs? Nat "constant")
  | "xor" => return .xor (← json.getObjValAs? Nat "constant")
  | "acc" => return .acc
  | "counter" => return .counter
  | _ => throw "unknown memory value operand"

def indexOf (json : Json) : Except String Index := do
  match ← json.getObjValAs? String "index" with
  | "literal" => return .literal (← json.getObjValAs? Nat "value")
  | "input" => return .input (← json.getObjValAs? Nat "shift") (← json.getObjValAs? Nat "modulus")
  | "counter" => return .counter (← json.getObjValAs? Nat "scale") (← json.getObjValAs? Nat "offset")
  | _ => throw "unknown memory value index"

def refOf (json : Json) : Except String Ref := do
  let text ← json.getStr?
  let number := fun (head : String) => do
    let digits := (text.drop head.length).toString
    let some value := digits.toNat? | throw "unknown memory value variable"
    unless toString value = digits do throw "noncanonical memory value variable"
    return value
  if text.startsWith "sc_b" then return .bytes (← number "sc_b")
  else if text.startsWith "sc_s" then return .slice (← number "sc_s")
  else if text.startsWith "sc_a" then return .array (← number "sc_a")
  else throw "unknown memory value variable"

def partOf (json : Json) : Except String Part := do
  match ← json.getObjValAs? String "part" with
  | "word" => return .word (← operandOf (← json.getObjVal? "operand"))
  | "zeros" => return .zeros (← json.getObjValAs? Nat "count")
  | "value" => return .value (← refOf (← json.getObjVal? "value"))
  | _ => throw "unknown memory value part"

def accessOf (json : Json) : Except String Access := do
  match ← json.getObjValAs? String "access" with
  | "length" => return .length
  | "word" => return .word (← indexOf (← json.getObjVal? "index"))
  | "byte" => return .byte (← indexOf (← json.getObjVal? "index"))
  | "hash" => return .hash
  | "element" =>
      let get ← match ← json.getObjValAs? String "form" with
        | "get" => pure true
        | "index" => pure false
        | _ => throw "unknown memory value element form"
      return .element (← indexOf (← json.getObjVal? "index")) get
  | _ => throw "unknown memory value access"

def actionOf (json : Json) : Except String Action := do
  match ← json.getObjValAs? String "kind" with
  | "bytes" =>
      let parts ← (← array json "parts").mapM partOf
      match ← json.getObjValAs? String "build", parts with
      | "to_bytes", [part] => return .bytes (.toBytes part)
      | "concat", [left, right] => return .bytes (.concat left right)
      | _, _ => throw "unknown memory value build"
  | "slice" =>
      let source ← refOf (← json.getObjVal? "source")
      match ← json.getObjValAs? String "cut" with
      | "drop" => return .slice source (.drop (← json.getObjValAs? Nat "start"))
      | "take" => return .slice source (.take (← json.getObjValAs? Nat "length"))
      | "window" => return .slice source (.window (← json.getObjValAs? Nat "start") (← json.getObjValAs? Nat "length"))
      | _ => throw "unknown memory value cut"
  | "alias" => return .alias (← refOf (← json.getObjVal? "source"))
  | "array" =>
      let allocated ← match ← json.getObjValAs? String "form" with
        | "allocated" => pure true
        | "literal" => pure false
        | _ => throw "unknown memory value array form"
      return .array allocated (← (← array json "elements").mapM operandOf)
  | "write" =>
      let width ← match ← json.getObjValAs? String "width" with
        | "word" => pure Width.word
        | "byte" => pure Width.byte
        | _ => throw "unknown memory value write width"
      let form ← match ← json.getObjValAs? String "form" with
        | "inline" => pure Form.inline
        | "helper" => pure Form.helper
        | _ => throw "unknown memory value write form"
      return .write (← refOf (← json.getObjVal? "target")) (← indexOf (← json.getObjVal? "index"))
        (← operandOf (← json.getObjVal? "value")) width form
  | "observe" =>
      let fold ← match ← json.getObjValAs? String "fold" with
        | "add" => pure Fold.add
        | "xor" => pure Fold.xor
        | _ => throw "unknown memory value fold"
      return .observe fold (← json.getObjValAs? Nat "constant") (← refOf (← json.getObjVal? "value"))
        (← accessOf (← json.getObjVal? "access"))
  | _ => throw "unknown memory value action"

def loopOf (json : Json) : Except String MemoryValues.Loop := do
  match ← json.getObjValAs? String "form" with
  | "single" => return .single (← json.getObjValAs? Nat "mask")
  | "nested" =>
      let bound ← match ← json.getObjValAs? String "bound" with
        | "input" => pure Bound.input
        | "counter" => pure Bound.counter
        | _ => throw "unknown memory value loop bound"
      return .nested (← json.getObjValAs? Nat "outer") bound (← json.getObjValAs? Nat "inner")
  | _ => throw "unknown memory value loop form"

def stepOf (json : Json) : Except String Step := do
  match json.getObjVal? "action" with
  | .ok action => return .action (← actionOf action)
  | .error _ => return .loop (← loopOf (← json.getObjVal? "loop")) (← (← array json "body").mapM actionOf)

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported memory value plan schema"
  return {steps := ← (← array json "steps").mapM stepOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "memory value plan is outside the admitted steps, values, lengths, indices and loops"
  let some checked := CheckedPlan.ofPlan? plan | throw "memory value reference failed the full Core checker"
  unless json == planJson plan do throw "saved memory value plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "memory value reference exceeds the 5,120-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

/-- A returned Word, or an out-of-range access. -/
inductive Outcome where
  | word (value : Word)
  | outOfRange
  deriving BEq

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done (.inLeft _ (.word word)) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done (.inRight _ (.word code)) _ =>
        match failureOutput? code with
        | some output => [("status", toJson "reverted"), ("output", toJson output)]
        | none => [("status", toJson "invalid-result"), ("detail", toJson s!"failure code {code.val}")]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("memoryValuePlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson memoryVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("memoryValueShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "memory value reference exceeds the 5,120-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic memory value case schema"
  let plan ← checkedPlan (← json.getObjVal? "memoryValuePlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its memory value plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.inLeft _ (.word value)) _ => .ok (.word value)
    | .done (.inRight _ (.word code)) _ =>
        if (failureOutput? code).isSome then .ok .outOfRange else .error "boundary observation failed with an unknown code"
    | .done _ _ => .error "boundary observation did not return a Word or an out-of-range access"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- At least two outcomes differ; with the identity filter, the Words are not
the inputs. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let outcomes ← boundaryOutcomes plan fuel
  unless outcomes.any (fun outcome => outcomes.any (fun other => outcome != other)) do
    throw "all eight boundary inputs had the same outcome"
  let words := outcomes.filterMap fun outcome => match outcome with
    | .word value => some value
    | .outOfRange => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the budgeted
reference exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.budgetNodes ≤ nodes do throw "memory value reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "memory value reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "memory-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
          throw "memory value node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "memory-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! Reduction. -/

/-- The lexicographic shrink measure: plan size, then input. -/
structure Measure where
  plan : Nat
  input : Nat
  deriving Repr, BEq, DecidableEq

def Measure.StrictlySmaller (candidate source : Measure) : Prop :=
  candidate.plan < source.plan ∨ (candidate.plan = source.plan ∧ candidate.input < source.input)

instance (candidate source : Measure) : Decidable (candidate.StrictlySmaller source) := by
  unfold Measure.StrictlySmaller
  infer_instance

def CheckedInput.measure (value : CheckedInput) : Measure := ⟨value.plan.plan.size, value.input.val⟩

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction (source : CheckedInput) (plan : Plan) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions with the input kept; then the inputs 0, 1 and half the
input with the plan kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (planReductions source.plan.plan).map (fun plan => (plan, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profileVersion), ("generatorVersion", memoryVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the memory value plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the memory value wrapper"
  unless (← provenance.getObjVal? "memoryValueShapes") == shapesJson admitted.plan.plan do
    throw "saved memory value shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "memory-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported memory value case origin"
  if kind = "memory-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved memory value plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw "generated memory value provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported memory value provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved memory value reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced memory value provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "memory value provenance contains unexpected fields"
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.MemoryValues
end
