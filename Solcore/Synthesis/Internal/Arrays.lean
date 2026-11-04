import Solcore.Synthesis.Internal.Integers
import Solcore.Synthesis.Internal.Functions

/-!
# Profiles: memory arrays

The profiles `runtime-memory-arrays` and `runtime-array-abi`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.Arrays
/-! std's memory arrays and slices in pure functions since solcore-rs
`e2eef194` (#145), the plans of the `runtime-memory-arrays` and
`runtime-array-abi` profiles: `T[]` of one of the twelve integer types made
with `new T[](n)`, literals, aliases, `toArray` copies and a helper's result;
element reads and writes, compound and unchecked ones and writes through a
`memref`; the four slice forms over arrays, slices, the storage array, grid
rows and calldata parameters; `T[][]` grids; a contract's storage array with
`push`, `pop` and `setLength`; one bounded loop over a collection's length;
and, for the second profile, `T[]` and `calldata<T[]>` parameters made from
the input Word and a `T[]` result.

The original Core reference holds an array as a length cell and its element
cells, so that an alias, a grid row and a memory parameter name the same
array, a slice reads through its base, and a copy is a new array. It checks
every index, slice bound, allocation and `pop` as std does, with Solidity's
panic codes, and checks a narrow calldata or memory parameter's elements as
std's ABI decoder does. It returns the left injection of the Words folded by
the source, or of the encoded `T[]`, or the right injection of the revert
data: its length and its bytes in two Words, the `runtime-revert-data`
encoding. Nothing here reads source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Arrays

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)
open Solcore.Synthesis.Core.Integers (IntType Op)

def arrayVersion : String := "core-arrays-v1"

/-! Plans. -/

/-- `sc_v<j>`: the input plus an offset converted to the element type, or as
it is when `raw`. -/
structure ValueInput where
  offset : Nat
  raw : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sc_k<j>`: `uint256(((sc_x >> shift) & mask))`, or when `flagged`,
`uint256((sc_x & (2^255 + mask)))`, which is at most `mask` or at least
`2^255`. -/
structure IndexInput where
  shift : Nat
  mask : Nat
  flagged : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A literal index, an index variable, or the loop's counter `sc_i`. -/
inductive Index where
  | literal (value : Nat)
  | input (index : Nat)
  | counter
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A value variable, or one of the element type's literals. -/
inductive Value where
  | input (index : Nat)
  | literal (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A literal length, or an index variable. -/
inductive Length where
  | literal (value : Nat)
  | input (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A memory array by name: `sc_a<j>`, or the memory parameter `sc_p<j>`. -/
inductive Name where
  | var (index : Nat)
  | param (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What `C.length` and `C[I]` read: an array, a slice `sc_s<j>`, the storage
array `sc_st`, a grid row `sc_g<g>[I]` or the calldata parameter `sc_p<j>`. -/
inductive Coll where
  | array (name : Name)
  | slice (index : Nat)
  | storage
  | row (grid : Nat) (index : Index)
  | calldata (index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What `A[I] = V;` writes. -/
inductive Target where
  | array (name : Name)
  | storage
  | row (grid : Nat) (index : Index)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `A[I] = V;`, `A[I] op= V;` alone or in an `unchecked` block,
`sc_put(lidx(A, I), V);` or `sc_inc(lidx(A, I), V);`. -/
inductive Form where
  | plain
  | compound (op : Op) (unchecked : Bool)
  | put
  | inc
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `B[S:E]`, `B[S:]`, `B[:E]` or `B[:]`. -/
inductive Cut where
  | range (start stop : Index)
  | start (start : Index)
  | stop (stop : Index)
  | all
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What the fold reads: `C.length`, `C[I]`, `sc_g<g>.length`,
`sc_sum(A)`, `sc_get(C, I)` or `sc_len(C)`. -/
inductive Observation where
  | length (coll : Coll)
  | element (coll : Coll) (index : Index)
  | gridLength (grid : Nat)
  | sum (name : Name)
  | get (coll : Coll) (index : Index)
  | len (coll : Coll)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a loop body may do, and a step outside it. -/
inductive Action where
  | write (target : Target) (index : Index) (value : Value) (form : Form)
  | observe (observation : Observation)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Step where
  | alloc (length : Length)
  | literal (values : List Value)
  | alias (source : Name)
  | copy (slice : Nat)
  | made (left right : Value)
  | slice (base : Coll) (cut : Cut)
  | tail (source : Name) (start : Index)
  | grid (length : Length)
  | gridOf (sources : List Name)
  | gridLiteral (rows : List (List Value))
  | setRow (grid : Nat) (index : Index) (source : Name)
  | act (action : Action)
  | fill (target : Name) (value : Value)
  | push (value : Value)
  | pop
  | setLength (length : Length)
  | loop (over : Coll) (body : List Action)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A parameter's length: a literal, or `((x >> shift) & mask)` of the input. -/
inductive ParamLength where
  | literal (value : Nat)
  | input (shift mask : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sc_p<j>`: `T[]` decoded into memory, or `calldata<T[]>`; element `k` is
`x + offset + k`, converted to the type unless `raw`. -/
structure Param where
  calldata : Bool
  length : ParamLength
  offset : Nat
  raw : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `uint256(sc_r)`, an array returned as `T[]`, or a slice's `toArray`. -/
inductive Result where
  | word
  | array (name : Name)
  | copy (slice : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  element : IntType
  values : List ValueInput
  indices : List IndexInput
  params : List Param
  steps : List Step
  result : Result
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Bounds. -/

def maximumSteps : Nat := 12
def maximumBound : Nat := 8
def maximumArrays : Nat := 4
def maximumSlices : Nat := 3
def maximumGrids : Nat := 2
def maximumValues : Nat := 3
def maximumIndices : Nat := 3
def maximumParams : Nat := 2
def maximumLiteral : Nat := 4
def maximumRows : Nat := 3
def maximumIndexLiteral : Nat := 7
def loopBound : Nat := 4
def maximumBody : Nat := 2
def indexShifts : List Nat := [0, 1, 2, 3, 8, 128, 253]
def indexMasks : List Nat := [1, 3, 7]
def flag : Nat := 2 ^ 255

/-- std's `newArrayP` panics with `0x41` for a length from here. -/
def allocationLimit : Nat := 2 ^ 251 - 1

/-- Return data Words: `0x20`, the length and up to eight elements. -/
def returnWords : Nat := 2 + maximumBound

/-! The static scope: the most elements each name can hold. -/

def Index.admitted (plan : Plan) (inLoop : Bool) : Index → Bool
  | .literal value => value ≤ maximumIndexLiteral
  | .input index => index < plan.indices.length
  | .counter => inLoop

def Value.admitted (plan : Plan) : Value → Bool
  | .input index => index < plan.values.length
  | .literal index => index < plan.element.literals.length

/-- A length's bound; a flagged index is a length only where `flagged`. -/
def Length.bound? (plan : Plan) (flagged : Bool) : Length → Option Nat
  | .literal value => if value ≤ maximumLiteral then some value else none
  | .input index => match plan.indices[index]? with
      | some entry => if entry.flagged && !flagged then none else some entry.mask
      | none => none

def ParamLength.bound : ParamLength → Nat
  | .literal value => value
  | .input _ mask => mask

def ParamLength.admitted : ParamLength → Bool
  | .literal value => value ≤ maximumLiteral
  | .input shift mask => indexShifts.contains shift && indexMasks.contains mask

def Cut.admitted (plan : Plan) : Cut → Bool
  | .range first last => first.admitted plan false && last.admitted plan false
  | .start first => first.admitted plan false
  | .stop last => last.admitted plan false
  | .all => true

/-- A slice's bound and what it reads through: the storage array, a calldata
parameter, or memory. -/
structure SliceInfo where
  bound : Nat
  storage : Bool
  calldata : Option Nat
  deriving Repr, BEq, Inhabited

/-- A grid's length bound and the bound of any of its rows. -/
structure GridInfo where
  bound : Nat
  rows : Nat
  deriving Repr, BEq, Inhabited

structure Scope where
  arrays : List Nat := []
  slices : List SliceInfo := []
  grids : List GridInfo := []
  storage : Nat := 0
  deriving Repr, BEq, Inhabited

private def need (condition : Bool) : Option Unit := if condition then some () else none

namespace Scope

def nameBound? (plan : Plan) (scope : Scope) : Name → Option Nat
  | .var index => scope.arrays[index]?
  | .param index => match plan.params[index]? with
      | some param => if param.calldata then none else some param.length.bound
      | none => none

def collBound? (plan : Plan) (storage inLoop : Bool) (scope : Scope) : Coll → Option Nat
  | .array name => scope.nameBound? plan name
  | .slice index => (scope.slices[index]?).map (·.bound)
  | .storage => if storage then some scope.storage else none
  | .row grid index => if index.admitted plan inLoop then (scope.grids[grid]?).map (·.rows) else none
  | .calldata index => match plan.params[index]? with
      | some param => if param.calldata then some param.length.bound else none
      | none => none

def targetBound? (plan : Plan) (storage inLoop : Bool) (scope : Scope) : Target → Option Nat
  | .array name => scope.nameBound? plan name
  | .storage => if storage then some scope.storage else none
  | .row grid index => if index.admitted plan inLoop then (scope.grids[grid]?).map (·.rows) else none

def observationAdmitted (plan : Plan) (storage inLoop : Bool) (scope : Scope) : Observation → Bool
  | .length coll | .len coll => (scope.collBound? plan storage inLoop coll).isSome
  | .element coll index | .get coll index =>
      (scope.collBound? plan storage inLoop coll).isSome && index.admitted plan inLoop
  | .gridLength grid => grid < scope.grids.length
  | .sum name => (scope.nameBound? plan name).isSome

def actionAdmitted (plan : Plan) (storage inLoop : Bool) (scope : Scope) : Action → Bool
  | .write target index value form =>
      (scope.targetBound? plan storage inLoop target).isSome && index.admitted plan inLoop && value.admitted plan &&
        (match form, target with
          | .put, .storage | .inc, .storage => false
          | _, _ => true)
  | .observe observation => scope.observationAdmitted plan storage inLoop observation

def withArray (scope : Scope) (bound : Nat) : Option Scope := do
  need (scope.arrays.length < maximumArrays && bound ≤ maximumBound)
  return {scope with arrays := scope.arrays ++ [bound]}

def withSlice (scope : Scope) (info : SliceInfo) : Option Scope := do
  need (scope.slices.length < maximumSlices)
  return {scope with slices := scope.slices ++ [info]}

def withGrid (scope : Scope) (info : GridInfo) : Option Scope := do
  need (scope.grids.length < maximumGrids && info.bound ≤ maximumBound)
  return {scope with grids := scope.grids ++ [info]}

/-- What a slice of a collection reads through. -/
def sliceInfo? (plan : Plan) (storage : Bool) (scope : Scope) (base : Coll) : Option SliceInfo := do
  let bound ← scope.collBound? plan storage false base
  match base with
  | .slice index => let inner ← scope.slices[index]?; return {inner with bound}
  | .storage => return {bound, storage := true, calldata := none}
  | .calldata index => return {bound, storage := false, calldata := some index}
  | _ => return {bound, storage := false, calldata := none}

/-- The scope after an admitted step, or `none`. -/
def step? (plan : Plan) (storage : Bool) (scope : Scope) : Step → Option Scope
  | .alloc length => do scope.withArray (← length.bound? plan true)
  | .literal values => do
      need (1 ≤ values.length && values.length ≤ maximumLiteral && values.all (·.admitted plan))
      scope.withArray values.length
  | .alias source => do scope.withArray (← scope.nameBound? plan source)
  | .copy slice => do scope.withArray (← scope.slices[slice]?).bound
  | .made left right => do
      need (left.admitted plan && right.admitted plan)
      scope.withArray 2
  | .slice base cut => do
      need (cut.admitted plan)
      scope.withSlice (← scope.sliceInfo? plan storage base)
  | .tail source start => do
      need (start.admitted plan false)
      scope.withSlice {bound := ← scope.nameBound? plan source, storage := false, calldata := none}
  | .grid length => do scope.withGrid {bound := ← length.bound? plan true, rows := 0}
  | .gridOf sources => do
      need (1 ≤ sources.length && sources.length ≤ maximumRows)
      let bounds ← sources.mapM (scope.nameBound? plan)
      scope.withGrid {bound := sources.length, rows := bounds.foldl max 0}
  | .gridLiteral rows => do
      need (1 ≤ rows.length && rows.length ≤ maximumRows &&
        rows.all (fun row => 1 ≤ row.length && row.length ≤ maximumRows && row.all (·.admitted plan)))
      scope.withGrid {bound := rows.length, rows := (rows.map (·.length)).foldl max 0}
  | .setRow grid index source => do
      let info ← scope.grids[grid]?
      let bound ← scope.nameBound? plan source
      need (index.admitted plan false)
      return {scope with grids := scope.grids.set grid {info with rows := max info.rows bound}}
  | .act action => do
      need (scope.actionAdmitted plan storage false action)
      return scope
  | .fill target value => do
      need ((scope.nameBound? plan target).isSome && value.admitted plan)
      return scope
  | .push value => do
      need (storage && value.admitted plan && scope.storage < maximumBound)
      return {scope with storage := scope.storage + 1}
  | .pop => do
      need storage
      return scope
  | .setLength length => do
      need storage
      return {scope with storage := ← length.bound? plan false}
  | .loop over body => do
      let bound ← scope.collBound? plan storage false over
      need (bound ≤ loopBound && 1 ≤ body.length && body.length ≤ maximumBody &&
        body.all (scope.actionAdmitted plan storage true))
      return scope

end Scope

namespace Action

def observes : Action → Bool
  | .observe _ => true
  | .write .. => false

/-- An element addition: a compound write or `sc_inc`. -/
def adds : Action → Bool
  | .write _ _ _ (.compound _ _) | .write _ _ _ .inc => true
  | .observe (.sum _) => true
  | _ => false

end Action

namespace Step

def actions : Step → List Action
  | .act action => [action]
  | .loop _ body => body
  | _ => []

def isLoop : Step → Bool
  | .loop .. => true
  | _ => false

def usesStorage : Step → Bool
  | .push _ | .pop | .setLength _ => true
  | .act (.write .storage _ _ _) => true
  | .slice .storage _ | .loop .storage _ => true
  | step => step.actions.any fun
      | .write .storage _ _ _ => true
      | .observe (.length .storage) | .observe (.len .storage) => true
      | .observe (.element .storage _) | .observe (.get .storage _) => true
      | _ => false

end Step

namespace Plan

def scan? (plan : Plan) (storage : Bool) : Option Scope :=
  plan.steps.foldlM (Scope.step? plan storage) {}

def observes (plan : Plan) : Bool := plan.steps.any fun step => step.actions.any (·.observes)

def usesStorage (plan : Plan) : Bool := plan.steps.any (·.usesStorage)

def common (plan : Plan) : Bool :=
  let type := plan.element
  type.admitted && 1 ≤ plan.values.length && plan.values.length ≤ maximumValues &&
    (plan.values.head?.map (·.offset)) == some 0 && plan.values.all (fun value => type.offsets.contains value.offset) &&
    plan.indices.length ≤ maximumIndices &&
    plan.indices.all (fun index => indexShifts.contains index.shift && indexMasks.contains index.mask &&
      (!index.flagged || index.shift == 0)) &&
    1 ≤ plan.steps.length && plan.steps.length ≤ maximumSteps && (plan.steps.filter (·.isLoop)).length ≤ 1

/-- A `runtime-memory-arrays` plan: no parameter, the fold, no raw value. -/
def memoryAdmitted (plan : Plan) : Bool :=
  plan.common && plan.params.isEmpty && plan.result == .word && plan.values.all (!·.raw) && plan.observes &&
    (plan.scan? true).isSome

def resultAdmitted (plan : Plan) (scope : Scope) : Result → Bool
  | .word => plan.observes
  | .array name => (scope.nameBound? plan name).isSome
  | .copy slice => slice < scope.slices.length

/-- A raw value or raw elements need a narrow type; a raw value also needs an
array result and no element addition. -/
def rawAdmitted (plan : Plan) : Bool :=
  let narrow := plan.element.bytes < 32
  (plan.params.all (fun param => !param.raw || narrow)) &&
    (plan.values.all (!·.raw) || (narrow && plan.result != .word &&
      !plan.steps.any (fun step => step.actions.any (·.adds))))

/-- A `runtime-array-abi` plan: one or two parameters, no storage array. -/
def abiAdmitted (plan : Plan) : Bool :=
  plan.common && 1 ≤ plan.params.length && plan.params.length ≤ maximumParams &&
    plan.params.all (fun param => param.length.admitted && plan.element.offsets.contains param.offset) &&
    plan.rawAdmitted &&
    match plan.scan? false with
    | some scope => plan.resultAdmitted scope plan.result
    | none => false

end Plan

/-! Words of the input: the values, indices and parameters it makes. -/

/-- A Word's 32 bytes, big-endian. -/
def wordBytes (value : Nat) : List Nat := (List.range 32).reverse.map fun index => (value / 256 ^ index) % 256

def ValueInput.word (type : IntType) (input : ValueInput) (x : Nat) : Nat :=
  let word := (x + input.offset) % 2 ^ 256
  if input.raw then word else type.convert word

def IndexInput.word (input : IndexInput) (x : Nat) : Nat :=
  if input.flagged then x &&& (flag + input.mask) else (x >>> input.shift) &&& input.mask

def ParamLength.word (length : ParamLength) (x : Nat) : Nat :=
  match length with
  | .literal value => value
  | .input shift mask => (x >>> shift) &&& mask

def Param.element (type : IntType) (param : Param) (x k : Nat) : Nat :=
  let word := (x + param.offset + k) % 2 ^ 256
  if param.raw then word else type.convert word

/-! Calldata: `run(uint256)`'s selector and the input, or the ABI encoding of
the parameters made from the input, then the input. -/

/-- `keccak256` of `run(uint256)`. -/
def memorySelector : Nat := 0xa444f5e9

/-- The selector of `run(T[],uint256)`, or of `run(T[],T[],uint256)` when
`two`: `keccak256` of the signature, pinned. -/
def abiSelector (type : IntType) (two : Bool) : Nat :=
  match type.signed, type.bytes, two with
  | false, 1, false => 0x8bd24abc | false, 1, true => 0x5434d13a
  | false, 2, false => 0xf9667762 | false, 2, true => 0xb80c6e47
  | false, 4, false => 0x6502c8b5 | false, 4, true => 0xc85caa6b
  | false, 8, false => 0xc7b78359 | false, 8, true => 0x980d964e
  | false, 16, false => 0x2e2e3fe9 | false, 16, true => 0x4317c184
  | false, _, false => 0xbb031b59 | false, _, true => 0xf8b1231b
  | true, 1, false => 0x57b6bce4 | true, 1, true => 0x25905c45
  | true, 2, false => 0x0b91d525 | true, 2, true => 0x83abf9bf
  | true, 4, false => 0x14240747 | true, 4, true => 0xbb1a6908
  | true, 8, false => 0x157e1f25 | true, 8, true => 0x438c7ad6
  | true, 16, false => 0x8018c529 | true, 16, true => 0x5f653335
  | true, _, false => 0x4fec41af | true, _, true => 0x0533c749

def selectorBytes (selector : Nat) : List Nat := (List.range 4).reverse.map fun index => (selector / 256 ^ index) % 256

namespace Plan

def selector (plan : Plan) : Nat :=
  if plan.params.isEmpty then memorySelector else abiSelector plan.element (plan.params.length = 2)

/-- The calldata at the input Word `x`. -/
def calldata (plan : Plan) (x : Nat) : List Nat :=
  let x := x % 2 ^ 256
  let lengths := plan.params.map (·.length.word x)
  let head := 32 * (plan.params.length + 1)
  let offsets := (lengths.foldl (fun (made : List Nat × Nat) length =>
    (made.1 ++ [made.2], made.2 + 32 * (1 + length))) ([], head)).1
  let tails := plan.params.zipIdx.flatMap fun (param, index) =>
    let length := lengths.getD index 0
    wordBytes length ++ (List.range length).flatMap fun k => wordBytes (param.element plan.element x k)
  selectorBytes plan.selector ++ offsets.flatMap wordBytes ++ wordBytes x ++ tails

end Plan

/-! A direct interpreter over Lean numbers, independent of the Core
reference: the shapes it reaches and the tests' second oracle. -/

/-- A run's outcome: the fold, the return data's bytes, a `Panic(code)`, or
std's ABI decoder's `DirtyHigherBitsForInteger()`. -/
inductive Outcome where
  | word (value : Nat)
  | output (bytes : List Nat)
  | panic (code : Nat)
  | dirty
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a run ended or what it encoded: the check that panicked or rejected,
and a returned element std's encoder had to mask or sign-extend. -/
inductive Event where
  | panic (site : String) (code : Nat)
  | dirty (site : String)
  | normalized
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An array: its length and element Words. -/
structure Obj where
  length : Nat
  items : List Nat
  deriving Repr, BEq, Inhabited

inductive Base where
  | heap (index : Nat)
  | storage
  | calldata (param : Nat)
  deriving Repr, BEq, Inhabited

structure SliceValue where
  base : Base
  start : Nat
  length : Nat
  deriving Repr, BEq, Inhabited

/-- The run's memory: the arrays, index 0 the shared empty array; what each
name, parameter, slice and grid slot holds; the storage array; the fold. -/
structure Machine where
  heap : Array Obj := #[{length := 0, items := []}]
  names : List Nat := []
  params : List (Option Nat) := []
  slices : List SliceValue := []
  grids : List (List Nat) := []
  storage : Obj := {length := 0, items := List.replicate maximumBound 0}
  acc : Nat := 0
  normalized : Bool := false
  deriving Inhabited

inductive Stop where
  | panic (code : Nat) (site : String)
  | dirty (site : String)
  deriving Repr, Inhabited

abbrev Run := StateT Machine (Except Stop)

private def fail {α : Type} (code : Nat) (site : String) : Run α := throw (.panic code site)

private def setItem (items : List Nat) (index value : Nat) : List Nat :=
  if index < items.length then items.set index value else items

/-- A resolved collection. -/
inductive Resolved where
  | heap (index : Nat)
  | storage
  | slice (value : SliceValue)
  | calldata (param : Nat)
  deriving Inhabited

structure Inputs where
  plan : Plan
  x : Nat
  values : List Nat
  indices : List Nat

namespace Inputs

def ofPlan (plan : Plan) (x : Nat) : Inputs :=
  {plan, x, values := plan.values.map (·.word plan.element x), indices := plan.indices.map (·.word x)}

def index (inputs : Inputs) (counter : Nat) : Index → Nat
  | .literal value => value
  | .input index => inputs.indices.getD index 0
  | .counter => counter

def value (inputs : Inputs) : Value → Nat
  | .input index => inputs.values.getD index 0
  | .literal index => IntType.rep (inputs.plan.element.literals.getD index 0)

def length (inputs : Inputs) : Length → Nat
  | .literal value => value
  | .input index => inputs.indices.getD index 0

def paramLength (inputs : Inputs) (param : Nat) : Nat :=
  match inputs.plan.params[param]? with
  | some value => value.length.word inputs.x
  | none => 0

def paramWord (inputs : Inputs) (param k : Nat) : Nat :=
  match inputs.plan.params[param]? with
  | some value => value.element inputs.plan.element inputs.x k
  | none => 0

end Inputs

namespace Machine

def obj (machine : Machine) (index : Nat) : Obj := machine.heap.getD index default

def named (machine : Machine) : Name → Nat
  | .var index => machine.names.getD index 0
  | .param index => (machine.params.getD index none).getD 0

end Machine

private def heapNew (obj : Obj) : Run Nat := modifyGet fun machine =>
  (machine.heap.size, {machine with heap := machine.heap.push obj})

private def heapSet (index : Nat) (obj : Obj) : Run Unit := modify fun machine =>
  {machine with heap := machine.heap.set! index obj}

def resolve (inputs : Inputs) (counter : Nat) : Coll → Run Resolved
  | .array name => do return .heap ((← get).named name)
  | .slice index => do return .slice ((← get).slices.getD index default)
  | .storage => pure .storage
  | .row grid index => do
      let slots := (← get).grids.getD grid []
      let position := inputs.index counter index
      if position < slots.length then return .heap (slots.getD position 0) else fail 0x32 "row"
  | .calldata param => pure (.calldata param)

def lengthOf (inputs : Inputs) : Resolved → Run Nat
  | .heap index => do return ((← get).obj index).length
  | .storage => do return (← get).storage.length
  | .slice value => pure value.length
  | .calldata param => pure (inputs.paramLength param)

/-- A calldata element after its index check: std's decoder rejects a
narrow element whose conversion differs from it. -/
private def calldataElement (inputs : Inputs) (param position : Nat) (site : String) : Run Nat := do
  let word := inputs.paramWord param position
  if inputs.plan.element.canonical word then return word else throw (.dirty site)

/-- `C[i]`: the index check, then a slice's base read at `start + i`. -/
def readAt (inputs : Inputs) (resolved : Resolved) (position : Nat) (site : String) (dirtySite : String := "read") :
    Run Nat := do
  match resolved with
  | .heap index =>
      let obj := (← get).obj index
      if position < obj.length then return obj.items.getD position 0 else fail 0x32 site
  | .storage =>
      let storage := (← get).storage
      if position < storage.length then return storage.items.getD position 0 else fail 0x32 site
  | .calldata param =>
      if position < inputs.paramLength param then calldataElement inputs param position dirtySite else fail 0x32 site
  | .slice value =>
      if value.length ≤ position then fail 0x32 "slice-read"
      let inner := value.start + position
      match value.base with
      | .heap index => return ((← get).obj index).items.getD inner 0
      | .storage =>
          let storage := (← get).storage
          if inner < storage.length then return storage.items.getD inner 0 else fail 0x32 "stale"
      | .calldata param => calldataElement inputs param inner dirtySite

def resolveTarget (inputs : Inputs) (counter : Nat) : Target → Run Resolved
  | .array name => do return .heap ((← get).named name)
  | .storage => pure .storage
  | .row grid index => resolve inputs counter (.row grid index)

private def store (resolved : Resolved) (position value : Nat) : Run Unit := do
  match resolved with
  | .heap index =>
      let obj := (← get).obj index
      heapSet index {obj with items := setItem obj.items position value}
  | .storage => modify fun machine =>
      {machine with storage := {machine.storage with items := setItem machine.storage.items position value}}
  | _ => pure ()

private def operated (type : IntType) (unchecked : Bool) (op : Op) (left right : Nat) (overflow : String) :
    Run Nat :=
  match Integers.operate type unchecked op (type.value left) (type.value right) with
  | .ok (rep, _) => pure rep
  | .error code => fail code (if code == 0x12 then "compound-zero" else overflow)

def write (inputs : Inputs) (counter : Nat) (target : Target) (index : Index) (value : Value) (form : Form) :
    Run Unit := do
  let resolved ← resolveTarget inputs counter target
  let position := inputs.index counter index
  let length ← lengthOf inputs resolved
  if length ≤ position then fail 0x32 "write"
  let type := inputs.plan.element
  let operand := inputs.value value
  let result ← match form with
    | .plain | .put => pure operand
    | .compound op unchecked => do
        operated type unchecked op (← readAt inputs resolved position "write") operand "compound-overflow"
    | .inc => do operated type false .add (← readAt inputs resolved position "write") operand "inc"
  store resolved position result

def sumOf (inputs : Inputs) (name : Name) : Run Nat := do
  let obj := (← get).obj ((← get).named name)
  let type := inputs.plan.element
  let mut total := 0
  for position in List.range obj.length do
    total ← operated type false .add total (obj.items.getD position 0) "sum"
  return total

def observation (inputs : Inputs) (counter : Nat) : Observation → Run Nat
  | .length coll | .len coll => do lengthOf inputs (← resolve inputs counter coll)
  | .element coll index | .get coll index => do
      readAt inputs (← resolve inputs counter coll) (inputs.index counter index) "read"
  | .gridLength grid => do return ((← get).grids.getD grid []).length
  | .sum name => sumOf inputs name

def act (inputs : Inputs) (counter : Nat) : Action → Run Unit
  | .write target index value form => write inputs counter target index value form
  | .observe observed => do
      let word ← observation inputs counter observed
      modify fun machine => {machine with acc := Integers.foldWord machine.acc word}

/-- `B[S:E]`: `start > end`, then `end > length`, panics with `0x32`; a slice
of a slice reads its base directly. -/
def slice (inputs : Inputs) (base : Coll) (cut : Cut) : Run SliceValue := do
  let resolved ← resolve inputs 0 base
  let length ← lengthOf inputs resolved
  let (start, stop) := match cut with
    | .range start stop => (inputs.index 0 start, inputs.index 0 stop)
    | .start start => (inputs.index 0 start, length)
    | .stop stop => (0, inputs.index 0 stop)
    | .all => (0, length)
  if stop < start then fail 0x32 "slice-start"
  if length < stop then fail 0x32 "slice-end"
  let size := stop - start
  match resolved with
  | .heap index => return {base := .heap index, start, length := size}
  | .storage => return {base := .storage, start, length := size}
  | .calldata param => return {base := .calldata param, start, length := size}
  | .slice inner => return {inner with start := inner.start + start, length := size}

def allocate (items : List Nat) : Run Nat := heapNew {length := items.length, items}

/-- `toArray(s)`: a new array of the slice's elements, read in order. -/
def copyOf (inputs : Inputs) (slice : SliceValue) (dirtySite : String) : Run Nat := do
  let mut items := []
  for position in List.range slice.length do
    items := items ++ [← readAt inputs (.slice slice) position "read" dirtySite]
  allocate items

def addName (index : Nat) : Run Unit := modify fun machine => {machine with names := machine.names ++ [index]}

def step (inputs : Inputs) : Step → Run Unit
  | .alloc length => do
      let size := inputs.length length
      if allocationLimit ≤ size then fail 0x41 "new"
      addName (← allocate (List.replicate size 0))
  | .literal values => do addName (← allocate (values.map inputs.value))
  | .alias source => do addName ((← get).named source)
  | .copy index => do addName (← copyOf inputs ((← get).slices.getD index default) "copy")
  | .made left right => do addName (← allocate [inputs.value left, inputs.value right])
  | .slice base cut => do
      let value ← slice inputs base cut
      modify fun machine => {machine with slices := machine.slices ++ [value]}
  | .tail source start => do
      let value ← slice inputs (.array source) (.start start)
      modify fun machine => {machine with slices := machine.slices ++ [value]}
  | .grid length => do
      let size := inputs.length length
      if allocationLimit ≤ size then fail 0x41 "grid-new"
      modify fun machine => {machine with grids := machine.grids ++ [List.replicate size 0]}
  | .gridOf sources => do
      let machine ← get
      set {machine with grids := machine.grids ++ [sources.map machine.named]}
  | .gridLiteral rows => do
      let mut slots := []
      for row in rows do
        slots := slots ++ [← allocate (row.map inputs.value)]
      modify fun machine => {machine with grids := machine.grids ++ [slots]}
  | .setRow grid index source => do
      let machine ← get
      let slots := machine.grids.getD grid []
      let position := inputs.index 0 index
      if slots.length ≤ position then fail 0x32 "row"
      set {machine with grids := machine.grids.set grid (slots.set position (machine.named source))}
  | .act action => act inputs 0 action
  | .fill target value => do
      let index := (← get).named target
      let obj := (← get).obj index
      heapSet index {obj with items := (List.range obj.items.length).map fun position =>
        if position < obj.length then inputs.value value else obj.items.getD position 0}
  | .push value => modify fun machine =>
      let storage := machine.storage
      {machine with storage := {length := storage.length + 1,
                                items := setItem storage.items storage.length (inputs.value value)}}
  | .pop => do
      let storage := (← get).storage
      if storage.length = 0 then fail 0x31 "pop"
      modify fun machine => {machine with storage := {length := storage.length - 1,
                                                      items := setItem storage.items (storage.length - 1) 0}}
  | .setLength length => do
      let size := inputs.length length
      modify fun machine =>
        let storage := machine.storage
        {machine with storage := {length := size, items := (List.range storage.items.length).map fun position =>
          if position < size then storage.items.getD position 0 else 0}}
  | .loop over body => do
      let mut counter := 0
      for _ in List.range (maximumBound + 1) do
        let length ← lengthOf inputs (← resolve inputs counter over)
        if length ≤ counter then break
        for action in body do act inputs counter action
        counter := counter + 1

/-- The ABI encoding of a returned array: `0x20`, the length and the
elements as std's encoder converts them. -/
def encode (type : IntType) (obj : Obj) : List Nat × Bool :=
  let elements := (List.range obj.length).map (obj.items.getD · 0)
  let words := [32, obj.length] ++ elements.map type.convert
  (words.flatMap wordBytes, elements.any (!type.canonical ·))

/-- Decode the memory parameters in order, each element checked as std's
decoder checks it. -/
def decode (inputs : Inputs) : Run Unit := do
  for (param, index) in inputs.plan.params.zipIdx do
    if param.calldata then
      modify fun machine => {machine with params := machine.params ++ [none]}
    else
      let items := (List.range (inputs.paramLength index)).map (inputs.paramWord index ·)
      unless items.all inputs.plan.element.canonical do throw (.dirty "memory")
      let slot ← allocate items
      modify fun machine => {machine with params := machine.params ++ [some slot]}

def body (inputs : Inputs) : Run Outcome := do
  decode inputs
  for value in inputs.plan.steps do step inputs value
  match inputs.plan.result with
  | .word =>
      let acc := (← get).acc
      return if inputs.plan.params.isEmpty then .word acc else .output (wordBytes acc)
  | .array name =>
      let (bytes, normalized) := encode inputs.plan.element ((← get).obj ((← get).named name))
      modify fun machine => {machine with normalized}
      return .output bytes
  | .copy index =>
      let copied ← copyOf inputs ((← get).slices.getD index default) "copy"
      let (bytes, normalized) := encode inputs.plan.element ((← get).obj copied)
      modify fun machine => {machine with normalized}
      return .output bytes

namespace Plan

/-- The outcome and events of a run at the input Word. -/
def run (plan : Plan) (input : Nat) : Outcome × List Event :=
  match (body (Inputs.ofPlan plan (input % 2 ^ 256))).run {} with
  | .ok (outcome, machine) => (outcome, if machine.normalized then [.normalized] else [])
  | .error (.panic code site) => (.panic code, [.panic site code])
  | .error (.dirty site) => (.dirty, [.dirty site])

def outcome (plan : Plan) (input : Nat) : Outcome := (plan.run input).1

end Plan

/-! The Core reference. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def int (value : Int) : Expr := .integer value
private def wadd (left right : Expr) : Expr := .binary .wordAdd left right
private def wsub (left right : Expr) : Expr := .binary .wordSub left right
private def wmul (left right : Expr) : Expr := .binary .wordMul left right
private def wand (left right : Expr) : Expr := .binary .wordAnd left right
private def wxor (left right : Expr) : Expr := .binary .wordXor left right
private def wshr (value shift : Expr) : Expr := .binary .wordShr value shift
/-- `left < right`. -/
private def below (left right : Expr) : Expr := .binary .wordGt right left
private def weq (left right : Expr) : Expr := .binary .wordEq left right
private def bnot (value : Expr) : Expr := .unary .boolNot value
private def both (left right : Expr) : Expr := .ifE left right (.bool false)
private def either (left right : Expr) : Expr := .ifE left (.bool true) right
private def ilt (left right : Expr) : Expr := .binary .integerLt left right
private def iadd (left right : Expr) : Expr := .binary .integerAdd left right
private def isub (left right : Expr) : Expr := .binary .integerSub left right
private def imul (left right : Expr) : Expr := .binary .integerMul left right
private def toWord (value : Expr) : Expr := .unary .integerToWord value

/-- `count` element cells, nested to the right. -/
def cellsTy : Nat → Ty
  | 0 => .unit
  | 1 => .cell .word
  | count + 2 => .product (.cell .word) (cellsTy (count + 1))

/-- An array: its length cell, then `maximumBound` element cells, those past
its bound the shared spare cell. -/
def arrayTy : Ty := .product (.cell .word) (cellsTy maximumBound)

def words : Nat → Ty
  | 0 => .unit
  | 1 => .word
  | count + 2 => .product .word (words (count + 1))

/-- `runtime-array-abi`'s return data: its length in bytes, then the Words. -/
def returnTy : Ty := words (1 + returnWords)

def Plan.leftTy (plan : Plan) : Ty := if plan.params.isEmpty then .word else returnTy

def Plan.resultTy (plan : Plan) : Ty := .sum plan.leftTy Integers.payloadType

def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value else field (index - 1) (count + 1) (.second value)

def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)

def lengthCell (array : Expr) : Expr := .first array

def elementCell (array : Expr) (index : Nat) : Expr := field index maximumBound (.second array)

/-- The cell of element `index` among an array's first `bound`, the last one
chosen for any other index; every access is checked first. -/
def selectCell (array : Expr) (bound : Nat) (index : Expr) : Expr :=
  if bound ≤ 1 then elementCell array 0
  else (List.range (bound - 1)).foldr (fun position rest =>
    .ifE (weq index (num position)) (elementCell array position) rest) (elementCell array (bound - 1))

abbrev Env := Integers.Env

/-- What a slice reads through: an array, the storage array when `storage`,
or a calldata parameter. -/
inductive BaseRef where
  | array (level bound : Nat) (storage : Bool)
  | calldata (param : Nat)
  deriving Inhabited

structure SliceRef where
  base : BaseRef
  start : Nat
  length : Nat
  bound : Nat
  deriving Inhabited

/-- A grid: its length Word, its slot cells and the bound of its rows. -/
structure GridRef where
  length : Nat
  slots : List Nat
  rows : Nat
  deriving Inhabited

inductive ParamRef where
  | memory (level bound : Nat)
  | calldata (length bound : Nat)
  deriving Inhabited

/-- The reference's binders by de Bruijn level. -/
structure Refs where
  input : Nat := 0
  spare : Nat := 0
  acc : Nat := 0
  empty : Nat := 0
  storage : Nat := 0
  storageBound : Nat := 0
  values : List Nat := []
  indices : List Nat := []
  params : List ParamRef := []
  arrays : List (Nat × Nat) := []
  slices : List SliceRef := []
  grids : List GridRef := []
  deriving Inhabited

/-- Inside the loop: the level of the iteration's guard and its counter. -/
structure Context where
  plan : Plan
  guard : Option Nat := none
  counter : Nat := 0

/-- A resolved collection. -/
inductive CollRef where
  | array (level bound : Nat) (storage : Bool)
  | slice (ref : SliceRef)
  | calldata (param : Nat)
  deriving Inhabited

namespace Context

def type (ctx : Context) : IntType := ctx.plan.element

def raise (ctx : Context) (payload : Expr) : Expr := .inRight ctx.plan.leftTy payload

def guarded (ctx : Context) (env : Env) (bad : Expr) : Expr :=
  match ctx.guard with
  | none => bad
  | some level => both (env.ref level) bad

/-- `rest` unless `bad`, which raises `Panic(code)` where the iteration runs. -/
def check (ctx : Context) (env : Env) (bad : Expr) (code : Nat) (rest : Expr) : Expr :=
  .ifE (ctx.guarded env bad) (ctx.raise (Integers.panicPayload code)) rest

def dirty (ctx : Context) (env : Env) (bad : Expr) (rest : Expr) : Expr :=
  .ifE (ctx.guarded env bad) (ctx.raise Integers.dirtyPayload) rest

/-- An effect where the iteration runs, then `rest`. -/
def effect (ctx : Context) (env : Env) (value : Expr) (rest : Env → Expr) : Expr :=
  env.bind (match ctx.guard with
    | none => value
    | some level => .ifE (env.ref level) value .unit) fun env _ => rest env

def index (ctx : Context) (refs : Refs) (env : Env) : Index → Expr
  | .literal value => num value
  | .input index => env.ref (refs.indices.getD index 0)
  | .counter => num ctx.counter

def value (ctx : Context) (refs : Refs) (env : Env) : Value → Expr
  | .input index => env.ref (refs.values.getD index 0)
  | .literal index => num (IntType.rep (ctx.type.literals.getD index 0))

def length (refs : Refs) (env : Env) : Length → Expr
  | .literal value => num value
  | .input index => env.ref (refs.indices.getD index 0)

/-- The array a name holds and its bound. -/
def named (refs : Refs) : Name → Nat × Nat
  | .var index => refs.arrays.getD index (0, 0)
  | .param index => match refs.params.getD index default with
      | .memory level bound => (level, bound)
      | .calldata _ _ => (0, 0)

/-- A calldata parameter's element `k`: the input plus its offset and `k`,
converted unless raw. -/
def paramWord (ctx : Context) (refs : Refs) (env : Env) (param : Nat) (position : Expr) : Expr :=
  let entry := ctx.plan.params.getD param default
  let word := wadd (wadd (env.ref refs.input) (num entry.offset)) position
  if entry.raw then word else Integers.convertExpr ctx.type word

def paramLength (refs : Refs) (env : Env) (param : Nat) : Expr :=
  match refs.params.getD param default with
  | .calldata length _ => env.ref length
  | .memory level _ => .loadCell (lengthCell (env.ref level))

def collLength (refs : Refs) (env : Env) : CollRef → Expr
  | .array level _ _ => .loadCell (lengthCell (env.ref level))
  | .slice ref => env.ref ref.length
  | .calldata param => paramLength refs env param

/-- A grid's slot cell at `index`, the last one for any other index. -/
def slotCell (grid : GridRef) (env : Env) (index : Expr) : Expr :=
  match grid.slots.getLast? with
  | none => .unit
  | some last => (grid.slots.dropLast.zipIdx).foldr (fun (slot, position) rest =>
      .ifE (weq index (num position)) (env.ref slot) rest) (env.ref last)

/-- A grid row: its row index checked against the grid's length, then the
array its slot holds. -/
def row (ctx : Context) (refs : Refs) (env : Env) (grid : Nat) (index : Index) (rest : Env → CollRef → Expr) : Expr :=
  let entry := refs.grids.getD grid default
  env.bind (ctx.index refs env index) fun env position =>
  ctx.check env (bnot (below (env.ref position) (env.ref entry.length))) 0x32 <|
  env.bind (.loadCell (slotCell entry env (env.ref position))) fun env value =>
    rest env (.array value entry.rows false)

def resolve (ctx : Context) (refs : Refs) (env : Env) (coll : Coll) (rest : Env → CollRef → Expr) : Expr :=
  match coll with
  | .array name => let (level, bound) := named refs name; rest env (.array level bound false)
  | .slice index => rest env (.slice (refs.slices.getD index default))
  | .storage => rest env (.array refs.storage refs.storageBound true)
  | .row grid index => ctx.row refs env grid index rest
  | .calldata param => rest env (.calldata param)

/-- A calldata element: narrow raw elements are checked as std's decoder
checks them. -/
def calldataRead (ctx : Context) (refs : Refs) (env : Env) (param : Nat) (position : Expr)
    (rest : Env → Nat → Expr) : Expr :=
  env.bind (ctx.paramWord refs env param position) fun env word =>
    if (ctx.plan.params.getD param default).raw then
      ctx.dirty env (bnot (weq (Integers.convertExpr ctx.type (env.ref word)) (env.ref word))) (rest env word)
    else rest env word

/-- `C[i]` after its index check; a slice checks its own length, then reads
its base at `start + i`, the storage array checked again. -/
def read (ctx : Context) (refs : Refs) (env : Env) (coll : CollRef) (position : Nat) (rest : Env → Nat → Expr) :
    Expr :=
  let outside := bnot (below (env.ref position) (collLength refs env coll))
  match coll with
  | .array level bound _ =>
      ctx.check env outside 0x32 <|
        env.bind (.loadCell (selectCell (env.ref level) bound (env.ref position))) rest
  | .calldata param => ctx.check env outside 0x32 <| ctx.calldataRead refs env param (env.ref position) rest
  | .slice ref =>
      ctx.check env outside 0x32 <|
      env.bind (wadd (env.ref ref.start) (env.ref position)) fun env inner =>
        match ref.base with
        | .array level bound storage =>
            let load := fun env => env.bind (.loadCell (selectCell (env.ref level) bound (env.ref inner))) rest
            if storage then
              ctx.check env (bnot (below (env.ref inner) (.loadCell (lengthCell (env.ref level))))) 0x32 (load env)
            else load env
        | .calldata param => ctx.calldataRead refs env param (env.ref inner) rest

/-- An integer operation on two representation Words: a zero divisor panics
with `0x12`, then the exact result is range-checked or wrapped. -/
def operation (ctx : Context) (env : Env) (unchecked : Bool) (op : Op) (left right : Nat)
    (rest : Env → Nat → Expr) : Expr :=
  let type := ctx.type
  let finish (env : Env) (result : Nat) : Expr :=
    if unchecked then env.bind (toWord (Integers.wrapExpr type (env.ref result))) rest
    else ctx.check env (either (ilt (env.ref result) (int type.minimum)) (ilt (int type.maximum) (env.ref result)))
      0x11 (env.bind (toWord (env.ref result)) rest)
  env.bind (Integers.readInt type (env.ref left)) fun env first =>
  env.bind (Integers.readInt type (env.ref right)) fun env second =>
    let compute (env : Env) : Expr := match op with
      | .add => env.bind (iadd (env.ref first) (env.ref second)) finish
      | .sub => env.bind (isub (env.ref first) (env.ref second)) finish
      | .mul => env.bind (imul (env.ref first) (env.ref second)) finish
      | .div => Integers.quotient env first second finish
      | .mod => Integers.quotient env first second fun env result =>
          env.bind (isub (env.ref first) (imul (env.ref second) (env.ref result))) finish
    if op == .div || op == .mod then
      ctx.check env (.binary .integerEq (env.ref second) (int 0)) 0x12 (compute env)
    else compute env

/-- `A[I] = V;` and its forms: the row's index, then the element's, then a
compound or `sc_inc` reads the element and computes before the store. -/
def write (ctx : Context) (refs : Refs) (env : Env) (target : Target) (index : Index) (value : Value) (form : Form)
    (rest : Env → Expr) : Expr :=
  let withTarget (env : Env) (level bound : Nat) : Expr :=
    env.bind (ctx.index refs env index) fun env position =>
    ctx.check env (bnot (below (env.ref position) (.loadCell (lengthCell (env.ref level))))) 0x32 <|
    env.bind (ctx.value refs env value) fun env operand =>
      let cell (env : Env) : Expr := selectCell (env.ref level) bound (env.ref position)
      let stored (env : Env) (word : Nat) : Expr := ctx.effect env (.storeCell (cell env) (env.ref word)) rest
      match form with
      | .plain | .put => stored env operand
      | .compound op unchecked =>
          env.bind (.loadCell (cell env)) fun env old => ctx.operation env unchecked op old operand stored
      | .inc => env.bind (.loadCell (cell env)) fun env old => ctx.operation env false .add old operand stored
  match target with
  | .array name => let (level, bound) := named refs name; withTarget env level bound
  | .storage => withTarget env refs.storage refs.storageBound
  | .row grid row => ctx.row refs env grid row fun env coll => match coll with
      | .array level bound _ => withTarget env level bound
      | _ => rest env

/-- `sc_sum(A)`: checked additions in order, the elements past the length
adding nothing. -/
def sum (ctx : Context) (env : Env) (level bound : Nat) (rest : Env → Nat → Expr) : Expr :=
  let type := ctx.type
  env.bind (.loadCell (lengthCell (env.ref level))) fun env length =>
  let rec go (env : Env) (position total : Nat) : Nat → Expr
    | 0 => env.bind (toWord (env.ref total)) rest
    | remaining + 1 =>
        let inside (env : Env) : Expr := below (num position) (env.ref length)
        env.bind (iadd (env.ref total) (.ifE (inside env)
            (Integers.readInt type (.loadCell (elementCell (env.ref level) position))) (int 0))) fun env next =>
          ctx.check env (both (inside env)
              (either (ilt (env.ref next) (int type.minimum)) (ilt (int type.maximum) (env.ref next))))
            0x11 (go env (position + 1) next remaining)
  env.bind (int 0) fun env total => go env 0 total bound

def observation (ctx : Context) (refs : Refs) (env : Env) (observed : Observation) (rest : Env → Nat → Expr) : Expr :=
  match observed with
  | .length coll | .len coll => ctx.resolve refs env coll fun env resolved => env.bind (collLength refs env resolved) rest
  | .element coll index | .get coll index =>
      ctx.resolve refs env coll fun env resolved =>
        env.bind (ctx.index refs env index) fun env position => ctx.read refs env resolved position rest
  | .gridLength grid => rest env (refs.grids.getD grid default).length
  | .sum name => let (level, bound) := named refs name; ctx.sum env level bound rest

def act (ctx : Context) (refs : Refs) (env : Env) (action : Action) (rest : Env → Expr) : Expr :=
  match action with
  | .write target index value form => ctx.write refs env target index value form rest
  | .observe observed => ctx.observation refs env observed fun env word =>
      ctx.effect env (.storeCell (env.ref refs.acc)
        (wxor (wmul (.loadCell (env.ref refs.acc)) (num Integers.foldConstant)) (env.ref word))) rest

end Context

/-- A new array of the given length Word and element Words, the cells past
them the spare cell. -/
def arrayValue (refs : Refs) (env : Env) (length : Expr) (items : List Expr) : Expr :=
  .pair (.newCell .word length) (packet ((List.range maximumBound).map fun position =>
    match items[position]? with
    | some item => .newCell .word item
    | none => env.ref refs.spare))

namespace Context

/-- `toArray(s)`: the slice's elements read in order, a storage base checked
against its current length and a narrow raw calldata element as std's decoder
checks it, into a new array of the slice's length. -/
def copy (ctx : Context) (refs : Refs) (env : Env) (ref : SliceRef) (rest : Env → Nat × Nat → Expr) : Expr :=
  let rec go (env : Env) (position : Nat) (items : List Nat) : Nat → Expr
    | 0 => env.bind (arrayValue refs env (env.ref ref.length) (items.map env.ref)) fun env level => rest env (level, ref.bound)
    | remaining + 1 =>
        let inside (env : Env) : Expr := below (num position) (env.ref ref.length)
        env.bind (wadd (env.ref ref.start) (num position)) fun env inner =>
        let next (env : Env) (word : Expr) : Expr :=
          env.bind (.ifE (inside env) word (num 0)) fun env item => go env (position + 1) (items ++ [item]) remaining
        match ref.base with
        | .array level bound storage =>
            let load := fun env => next env (.loadCell (selectCell (env.ref level) bound (env.ref inner)))
            if storage then
              ctx.check env (both (inside env) (bnot (below (env.ref inner) (.loadCell (lengthCell (env.ref level))))))
                0x32 (load env)
            else load env
        | .calldata param =>
            env.bind (ctx.paramWord refs env param (env.ref inner)) fun env word =>
              if (ctx.plan.params.getD param default).raw then
                ctx.dirty env (both (inside env)
                    (bnot (weq (Integers.convertExpr ctx.type (env.ref word)) (env.ref word))))
                  (next env (env.ref word))
              else next env (env.ref word)
  go env 0 [] ref.bound

/-- `B[S:E]`: the base (a row's index first), then `start > end` and
`end > length` panic with `0x32`; a slice of a slice reads the inner base. -/
def slice (ctx : Context) (refs : Refs) (env : Env) (base : Coll) (cut : Cut) (bound : Nat)
    (rest : Env → SliceRef → Expr) : Expr :=
  ctx.resolve refs env base fun env resolved =>
  env.bind (collLength refs env resolved) fun env length =>
  let first (env : Env) : Expr := match cut with
    | .range start _ | .start start => ctx.index refs env start
    | .stop _ | .all => num 0
  let last (env : Env) : Expr := match cut with
    | .range _ stop | .stop stop => ctx.index refs env stop
    | .start _ | .all => env.ref length
  env.bind (first env) fun env start =>
  env.bind (last env) fun env stop =>
  ctx.check env (below (env.ref stop) (env.ref start)) 0x32 <|
  ctx.check env (below (env.ref length) (env.ref stop)) 0x32 <|
  env.bind (wsub (env.ref stop) (env.ref start)) fun env size =>
    match resolved with
    | .array level arrayBound storage =>
        rest env {base := .array level arrayBound storage, start, length := size, bound}
    | .calldata param => rest env {base := .calldata param, start, length := size, bound}
    | .slice inner =>
        env.bind (wadd (env.ref inner.start) (env.ref start)) fun env offset =>
          rest env {base := inner.base, start := offset, length := size, bound}

/-- New slot cells, each holding an array. -/
def slots (env : Env) (values : List (Env → Expr)) (rest : Env → List Nat → Expr) : Expr :=
  let rec go (env : Env) (made : List Nat) : List (Env → Expr) → Expr
    | [] => rest env made
    | value :: more => env.bind (.newCell arrayTy (value env)) fun env slot => go env (made ++ [slot]) more
  go env [] values

end Context

namespace Plan

/-- The storage array's bound and each slice's and grid row's, from the
admitted scope. -/
def storageBound (plan : Plan) : Nat := Id.run do
  let mut scope : Scope := {}
  let mut most := 0
  for step in plan.steps do
    match scope.step? plan true step with
    | some next => scope := next; most := max most next.storage
    | none => pure ()
  return most

/-- The steps, every helper inlined where it runs. -/
def compile (ctx : Context) (scopes : List Scope) : Refs → Env → List Step → (Refs → Env → Expr) → Expr
  | refs, env, [], finish => finish refs env
  | refs, env, step :: rest, finish =>
      let scope := scopes.headD {}
      let bound (coll : Coll) : Nat := (scope.collBound? ctx.plan true false coll).getD 0
      let next (refs : Refs) (env : Env) : Expr := compile ctx scopes.tail refs env rest finish
      let named (refs : Refs) (env : Env) (level bound : Nat) : Expr :=
        next {refs with arrays := refs.arrays ++ [(level, bound)]} env
      match step with
      | .alloc length =>
          let size := (length.bound? ctx.plan true).getD 0
          env.bind (Context.length refs env length) fun env count =>
          ctx.check env (bnot (below (env.ref count) (num allocationLimit))) 0x41 <|
          env.bind (arrayValue refs env (env.ref count) ((List.range size).map fun _ => num 0)) fun env level =>
            named refs env level size
      | .literal values =>
          env.bind (arrayValue refs env (num values.length) (values.map (ctx.value refs env))) fun env level =>
            named refs env level values.length
      | .alias source => let (level, size) := Context.named refs source; named refs env level size
      | .copy slice => ctx.copy refs env (refs.slices.getD slice default) fun env (level, size) => named refs env level size
      | .made left right =>
          env.bind (arrayValue refs env (num 2) [ctx.value refs env left, ctx.value refs env right]) fun env level =>
            named refs env level 2
      | .slice base cut =>
          ctx.slice refs env base cut (bound base) fun env ref => next {refs with slices := refs.slices ++ [ref]} env
      | .tail source start =>
          ctx.slice refs env (.array source) (.start start) (bound (.array source)) fun env ref =>
            next {refs with slices := refs.slices ++ [ref]} env
      | .grid length =>
          let size := (length.bound? ctx.plan true).getD 0
          env.bind (Context.length refs env length) fun env count =>
          ctx.check env (bnot (below (env.ref count) (num allocationLimit))) 0x41 <|
          Context.slots env ((List.range (max size 1)).map fun _ env => env.ref refs.empty) fun env cells =>
            next {refs with grids := refs.grids ++ [{length := count, slots := cells, rows := 0}]} env
      | .gridOf sources =>
          let arrays := sources.map (Context.named refs)
          env.bind (num sources.length) fun env count =>
          Context.slots env (arrays.map fun (level, _) env => env.ref level) fun env cells =>
            next {refs with grids := refs.grids ++ [{length := count, slots := cells,
                                                     rows := (arrays.map (·.2)).foldl max 0}]} env
      | .gridLiteral rows =>
          let rec made (env : Env) (levels : List Nat) : List (List Value) → Expr
            | [] =>
                env.bind (num rows.length) fun env count =>
                Context.slots env (levels.map fun level env => env.ref level) fun env cells =>
                  next {refs with grids := refs.grids ++ [{length := count, slots := cells,
                                                           rows := (rows.map (·.length)).foldl max 0}]} env
            | row :: more =>
                env.bind (arrayValue refs env (num row.length) (row.map (ctx.value refs env))) fun env level =>
                  made env (levels ++ [level]) more
          made env [] rows
      | .setRow grid index source =>
          let entry := refs.grids.getD grid default
          let (level, size) := Context.named refs source
          env.bind (ctx.index refs env index) fun env position =>
          ctx.check env (bnot (below (env.ref position) (env.ref entry.length))) 0x32 <|
          ctx.effect env (.storeCell (Context.slotCell entry env (env.ref position)) (env.ref level)) fun env =>
            next {refs with grids := refs.grids.set grid {entry with rows := max entry.rows size}} env
      | .act action => ctx.act refs env action fun env => next refs env
      | .fill target value =>
          let (level, size) := Context.named refs target
          env.bind (.loadCell (lengthCell (env.ref level))) fun env count =>
          env.bind (ctx.value refs env value) fun env word =>
          let rec fillFrom (env : Env) (position : Nat) : Nat → Expr
            | 0 => next refs env
            | remaining + 1 =>
                env.bind (.ifE (below (num position) (env.ref count))
                    (.storeCell (elementCell (env.ref level) position) (env.ref word)) .unit) fun env _ =>
                  fillFrom env (position + 1) remaining
          fillFrom env 0 size
      | .push value =>
          let storage := refs.storage
          env.bind (.loadCell (lengthCell (env.ref storage))) fun env count =>
          env.bind (.storeCell (selectCell (env.ref storage) refs.storageBound (env.ref count)) (ctx.value refs env value))
            fun env _ =>
          env.bind (.storeCell (lengthCell (env.ref storage)) (wadd (env.ref count) (num 1))) fun env _ => next refs env
      | .pop =>
          let storage := refs.storage
          env.bind (.loadCell (lengthCell (env.ref storage))) fun env count =>
          ctx.check env (weq (env.ref count) (num 0)) 0x31 <|
          env.bind (wsub (env.ref count) (num 1)) fun env last =>
          env.bind (.storeCell (selectCell (env.ref storage) refs.storageBound (env.ref last)) (num 0)) fun env _ =>
          env.bind (.storeCell (lengthCell (env.ref storage)) (env.ref last)) fun env _ => next refs env
      | .setLength length =>
          let storage := refs.storage
          env.bind (Context.length refs env length) fun env count =>
          env.bind (.storeCell (lengthCell (env.ref storage)) (env.ref count)) fun env _ =>
          let rec clearFrom (env : Env) (position : Nat) : Nat → Expr
            | 0 => next refs env
            | remaining + 1 =>
                env.bind (.ifE (below (num position) (env.ref count)) .unit
                    (.storeCell (elementCell (env.ref storage) position) (num 0))) fun env _ =>
                  clearFrom env (position + 1) remaining
          clearFrom env 0 refs.storageBound
      | .loop over body =>
          let iterations := bound over
          ctx.resolve refs env over fun env resolved =>
          env.bind (Context.collLength refs env resolved) fun env count =>
          let rec iterate (env : Env) (counter : Nat) : Nat → Expr
            | 0 => next refs env
            | remaining + 1 =>
                env.bind (below (num counter) (env.ref count)) fun env guard =>
                let inner : Context := {ctx with guard := some guard, counter}
                let rec actions (env : Env) : List Action → Expr
                  | [] => iterate env (counter + 1) remaining
                  | action :: more => inner.act refs env action fun env => actions env more
                actions env body
          iterate env 0 iterations

/-- The admitted scope before each step. -/
def scopes (plan : Plan) : List Scope := Id.run do
  let storage := plan.params.isEmpty
  let mut scope : Scope := {}
  let mut result := []
  for step in plan.steps do
    result := result ++ [scope]
    scope := (scope.step? plan storage step).getD scope
  return result

/-- The memory parameters decoded in order, a narrow raw element checked as
std's decoder checks it; a calldata parameter is only its length. -/
def bindParams (ctx : Context) : Refs → Env → List (Param × Nat) → (Refs → Env → Expr) → Expr
  | refs, env, [], rest => rest refs env
  | refs, env, (param, _) :: more, rest =>
      let size := param.length.bound
      let lengthWord : Expr := match param.length with
        | .literal value => num value
        | .input shift mask => wand (wshr (env.ref refs.input) (num shift)) (num mask)
      env.bind lengthWord fun env count =>
        if param.calldata then
          bindParams ctx {refs with params := refs.params ++ [.calldata count size]} env more rest
        else
          let element (env : Env) (position : Nat) : Expr :=
            let word := wadd (env.ref refs.input) (num (param.offset + position))
            if param.raw then word else Integers.convertExpr ctx.type word
          let bad (env : Env) : Expr := (List.range size).foldr (fun position rest =>
            either (both (below (num position) (env.ref count))
              (bnot (weq (Integers.convertExpr ctx.type (element env position)) (element env position)))) rest)
            (.bool false)
          let decoded (env : Env) : Expr :=
            env.bind (arrayValue refs env (env.ref count) ((List.range size).map fun position =>
                .ifE (below (num position) (env.ref count)) (element env position) (num 0))) fun env level =>
              bindParams ctx {refs with params := refs.params ++ [.memory level size]} env more rest
          if param.raw then .ifE (bad env) (ctx.raise Integers.dirtyPayload) (decoded env) else decoded env

/-- The returned array: `0x20`, its length and its elements converted as std's
encoder converts them, and the data's length in bytes. -/
def returned (ctx : Context) (env : Env) (level : Nat) : Expr :=
  let length := Expr.loadCell (lengthCell (env.ref level))
  .inLeft Integers.payloadType (packet ([wadd (num 64) (wmul (num 32) length), num 32, length] ++
    (List.range maximumBound).map fun position =>
      .ifE (below (num position) length)
        (Integers.convertExpr ctx.type (.loadCell (elementCell (env.ref level) position))) (num 0)))

def finish (ctx : Context) (refs : Refs) (env : Env) : Expr :=
  let plan := ctx.plan
  match plan.result with
  | .word =>
      let acc := Expr.loadCell (env.ref refs.acc)
      .inLeft Integers.payloadType (if plan.params.isEmpty then acc
        else packet ([num 32, acc] ++ (List.range (returnWords - 1)).map fun _ => num 0))
  | .array name => returned ctx env (Context.named refs name).1
  | .copy slice => ctx.copy refs env (refs.slices.getD slice default) fun env (level, _) => returned ctx env level

/-- `fun input => …`: the spare cell, the fold's cell, the shared empty array
and the storage array, the values and indices, the decoded parameters, every
step, then the result's left injection; a panic or a decoder's rejection is
the right injection of its revert data. -/
def expression (plan : Plan) : Expr :=
  let ctx : Context := {plan}
  let env : Env := {depth := 1}
  let storageBound := plan.storageBound
  let body :=
    env.bind (.newCell .word (num 0)) fun env spare =>
    env.bind (.newCell .word (num 0)) fun env acc =>
    let refs : Refs := {input := 0, spare, acc}
    env.bind (arrayValue refs env (num 0) []) fun env empty =>
    let refs := {refs with empty}
    env.bind (arrayValue refs env (num 0) ((List.range storageBound).map fun _ => num 0)) fun env storage =>
    let refs := {refs with storage, storageBound}
    let rec values (refs : Refs) (env : Env) : List ValueInput → Expr
      | [] =>
          let rec indices (refs : Refs) (env : Env) : List IndexInput → Expr
            | [] => bindParams ctx refs env plan.params.zipIdx fun refs env =>
                compile ctx plan.scopes refs env plan.steps (finish ctx)
            | input :: more =>
                let word := if input.flagged then wand (env.ref refs.input) (num (flag + input.mask))
                  else wand (wshr (env.ref refs.input) (num input.shift)) (num input.mask)
                env.bind word fun env level => indices {refs with indices := refs.indices ++ [level]} env more
          indices refs env plan.indices
      | input :: more =>
          let word := wadd (env.ref refs.input) (num input.offset)
          env.bind (if input.raw then word else Integers.convertExpr plan.element word) fun env level =>
            values {refs with values := refs.values ++ [level]} env more
    values refs env plan.values
  .lambda .word plan.resultTy body

def program (plan : Plan) : Program := {
  resultType := .function .word plan.resultTy, dataDefinitions := [], body := plan.expression}

def applied (plan : Plan) (input : Word) : Program := {
  resultType := plan.resultTy, dataDefinitions := [], body := .apply plan.expression (.word input)}

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

end Plan

/-! Specified shapes: the plan's own values, and those its run reaches at the
eight boundary inputs, never measured on a compiled path. -/

private def sorted (values : List String) : List String :=
  (values.foldl (fun seen value => if seen.contains value then seen else seen ++ [value]) []).mergeSort (· ≤ ·)

def Cut.shape : Cut → String
  | .range .. => "slice-range"
  | .start _ => "slice-from"
  | .stop _ => "slice-to"
  | .all => "slice-all"

def Coll.shape : Coll → String
  | .array _ => "array"
  | .slice _ => "slice"
  | .storage => "storage"
  | .row .. => "row"
  | .calldata _ => "calldata"

def Target.shape : Target → String
  | .array _ => "array"
  | .storage => "storage"
  | .row .. => "row"

def Form.shape : Form → String
  | .plain => "plain"
  | .compound op unchecked => (if unchecked then "unchecked-" else "") ++ op.name
  | .put => "put"
  | .inc => "inc"

def Observation.shape : Observation → String
  | .length _ => "length"
  | .element .. => "element"
  | .gridLength _ => "grid-length"
  | .sum _ => "sum"
  | .get .. => "get"
  | .len _ => "len"

def Observation.coll? : Observation → Option Coll
  | .length coll | .element coll _ | .get coll _ | .len coll => some coll
  | _ => none

def Observation.indices : Observation → List Index
  | .element _ index | .get _ index => [index]
  | _ => []

def Coll.indices : Coll → List Index
  | .row _ index => [index]
  | _ => []

def Target.indices : Target → List Index
  | .row _ index => [index]
  | _ => []

def Action.indices : Action → List Index
  | .write target index _ _ => target.indices ++ [index]
  | .observe observation => ((observation.coll?.map (·.indices)).getD []) ++ observation.indices

def Cut.indices : Cut → List Index
  | .range first last => [first, last]
  | .start first => [first]
  | .stop last => [last]
  | .all => []

def Step.indices : Step → List Index
  | .slice base cut => base.indices ++ cut.indices
  | .tail _ start => [start]
  | .setRow _ index _ => [index]
  | .act action => action.indices
  | .loop over body => over.indices ++ body.flatMap (·.indices)
  | _ => []

def Step.lengths : Step → List Length
  | .alloc length | .grid length | .setLength length => [length]
  | _ => []

def Step.declaration? : Step → Option String
  | .alloc _ => some "new"
  | .literal _ => some "literal"
  | .alias _ => some "alias"
  | .copy _ => some "copy"
  | .made .. => some "helper"
  | .slice _ cut => some cut.shape
  | .tail .. => some "tail"
  | .grid _ => some "grid-new"
  | .gridOf _ => some "grid-arrays"
  | .gridLiteral _ => some "grid-literal"
  | _ => none

def Step.writes : Step → List String
  | .fill .. => ["fill"]
  | .setRow .. => ["set-row"]
  | step => step.actions.filterMap fun
      | .write _ _ _ form => some form.shape
      | .observe _ => none

def Step.member? : Step → Option String
  | .push _ => some "push"
  | .pop => some "pop"
  | .setLength _ => some "set-length"
  | _ => none

namespace Plan

def boundaryRuns (plan : Plan) : List (Outcome × List Event) := Integers.boundaryWords.map plan.run

def indexShape (plan : Plan) : Index → String
  | .literal _ => "literal"
  | .input index => if ((plan.indices[index]?).map (·.flagged)).getD false then "flagged" else "input"
  | .counter => "counter"

def lengthShape (plan : Plan) : Length → String
  | .literal _ => "literal"
  | .input index => if ((plan.indices[index]?).map (·.flagged)).getD false then "flagged" else "input"

def outcomeName : Outcome → String
  | .word _ | .output _ => "returned"
  | .panic code => "panic-0x" ++ String.ofList (Nat.toDigits 16 code)
  | .dirty => "dirty"

def collections (plan : Plan) : List Coll :=
  plan.steps.flatMap fun step =>
    (match step with
      | .loop over _ => [over]
      | _ => []) ++ step.actions.filterMap fun
        | .observe observation => observation.coll?
        | .write .. => none

def bases (plan : Plan) : List String :=
  plan.steps.filterMap fun
    | .slice base _ => some base.shape
    | .tail .. => some "array"
    | _ => none

/-- An array's identity at each declaration, so that two names of one array
are known; a parameter's identity is its number. -/
def identities (plan : Plan) : List Nat := Id.run do
  let mut arrays : List Nat := []
  let mut fresh := plan.params.length
  for step in plan.steps do
    match step with
    | .alias source => arrays := arrays ++ [match source with
        | .var index => arrays.getD index 0
        | .param index => index]
    | .alloc _ | .literal _ | .copy _ | .made .. => arrays := arrays ++ [fresh]; fresh := fresh + 1
    | _ => pure ()
  return arrays

def identity (plan : Plan) (name : Name) : Nat :=
  match name with
  | .var index => plan.identities.getD index 0
  | .param index => index

/-- The plan's sharing, by position: a write through one name of an array
seen through another (`alias`), through a grid row and the array it holds
(`row`), a write to a slice's base seen through the slice (`view`), and a
copy that a later write to its source or to itself leaves apart (`copy`). -/
def sharing (plan : Plan) : List String := Id.run do
  let steps := plan.steps
  let positions := steps.zipIdx
  let writes : List (Nat × Target) := positions.flatMap fun (step, position) =>
    (step.actions.filterMap fun
      | .write target _ _ _ => some (position, target)
      | .observe _ => none) ++
    (match step with
      | .fill target _ => [(position, Target.array target)]
      | .push _ | .pop | .setLength _ => [(position, Target.storage)]
      | _ => [])
  let observations : List (Nat × Coll) := positions.flatMap fun (step, position) =>
    step.actions.filterMap fun
      | .observe observation => (observation.coll?.map (position, ·)).orElse fun _ => match observation with
          | .sum name => some (position, Coll.array name)
          | _ => none
      | .write .. => none
  let gridArrays (grid : Nat) : List Nat := positions.foldl (fun (found : List (List Nat)) (step, _) =>
      match step with
      | .grid _ | .gridLiteral _ => found ++ [[]]
      | .gridOf sources => found ++ [sources.map plan.identity]
      | .setRow index _ source => found.set index ((found.getD index []) ++ [plan.identity source])
      | _ => found) [] |>.getD grid []
  let mut result := []
  for (step, position) in positions do
    match step with
    | .alias source =>
        let alias := plan.identity source
        if writes.any (fun (written, target) => position < written && (match target with
            | .array name => plan.identity name == alias && observations.any (fun (seen, coll) =>
                written < seen && (match coll with
                  | .array other => plan.identity other == alias && other != name
                  | _ => false))
            | _ => false)) then
          result := result ++ ["alias"]
    | .gridOf _ | .setRow .. | .gridLiteral _ =>
        pure ()
    | .slice base _ =>
        if writes.any (fun (written, target) => position < written && (match base, target with
            | .array name, .array other => plan.identity name == plan.identity other
            | .storage, .storage => true
            | _, _ => false) && observations.any (fun (seen, coll) => written < seen && coll matches .slice _)) then
          result := result ++ ["view"]
    | .copy _ =>
        if writes.any (fun (later, _) => position < later) && observations.any (fun (later, _) => position < later) then
          result := result ++ ["copy"]
    | _ => pure ()
  let rows := (List.range maximumGrids).any fun grid =>
    let arrays := gridArrays grid
    (writes.any fun (later, target) => match target with
      | .row index _ => index == grid && observations.any (fun (seen, coll) => later < seen && (match coll with
          | .array name => arrays.contains (plan.identity name)
          | _ => false))
      | .array name => arrays.contains (plan.identity name) && observations.any (fun (seen, coll) =>
          later < seen && (match coll with
          | .row index _ => index == grid
          | _ => false))
      | .storage => false)
  return sorted (result ++ (if rows then ["row"] else []))

def panicSites (runs : List (Outcome × List Event)) : List String :=
  runs.flatMap fun (_, events) => events.filterMap fun
    | .panic site _ => some site
    | _ => none

def dirtySites (runs : List (Outcome × List Event)) : List String :=
  runs.flatMap fun (_, events) => events.filterMap fun
    | .dirty site => some site
    | _ => none

/-- The `runtime-memory-arrays` shapes. -/
def memoryShapes (plan : Plan) : List (String × List String) :=
  let steps := plan.steps
  let actions := steps.flatMap (·.actions)
  let runs := plan.boundaryRuns
  [("types", [plan.element.name]),
    ("declarations", sorted (steps.filterMap (·.declaration?))),
    ("writes", sorted (steps.flatMap (·.writes))),
    ("targets", sorted (actions.filterMap fun
      | .write target _ _ _ => some target.shape
      | .observe _ => none)),
    ("members", sorted (steps.filterMap (·.member?))),
    ("observations", sorted (actions.filterMap fun
      | .observe observation => some observation.shape
      | .write .. => none)),
    ("collections", sorted (plan.collections.map (·.shape))),
    ("bases", sorted plan.bases),
    ("indices", sorted ((steps.flatMap (·.indices)).map plan.indexShape)),
    ("lengths", sorted ((steps.flatMap (·.lengths)).map plan.lengthShape)),
    ("loops", sorted (steps.filterMap fun
      | .loop over _ => some over.shape
      | _ => none)),
    ("sharing", plan.sharing),
    ("outcomes", sorted (runs.map (outcomeName ·.1))),
    ("panics", sorted (panicSites runs))]

/-- What a calldata parameter is read by. -/
def calldataReads (plan : Plan) : List String :=
  let steps := plan.steps
  let viaCalldata (index : Nat) : Bool := match plan.scopes[index]? with
    | some scope => match steps[index]? with
        | some (.copy slice) => ((scope.slices[slice]?).bind (·.calldata)).isSome
        | _ => false
    | none => false
  let copies := (List.range steps.length).any viaCalldata ||
    (match plan.result with
      | .copy slice => ((((plan.scan? false).map (·.slices)).getD [])[slice]?.bind (·.calldata)).isSome
      | _ => false)
  (steps.flatMap fun step => match step with
    | .slice (.calldata _) _ => ["slice"]
    | .loop (.calldata _) body => "loop" :: body.filterMap fun
        | .observe (.element (.calldata _) _) => some "element"
        | _ => none
    | _ => step.actions.filterMap fun
        | .observe (.length (.calldata _)) | .observe (.len (.calldata _)) => some "length"
        | .observe (.element (.calldata _) _) => some "element"
        | .observe (.get (.calldata _) _) => some "get"
        | _ => none) ++ (if copies then ["copy"] else [])

/-- The writes into a memory parameter, through its name. -/
def parameterWrites (plan : Plan) : List String :=
  plan.steps.flatMap fun step => match step with
    | .fill (.param _) _ => ["fill"]
    | _ => step.actions.filterMap fun
        | .write (.array (.param _)) _ _ form => some (match form with
            | .plain => "plain"
            | .compound .. => "compound"
            | .put | .inc => "memref")
        | _ => none

/-- The `runtime-array-abi` shapes. -/
def abiShapes (plan : Plan) : List (String × List String) :=
  let runs := plan.boundaryRuns
  [("types", [plan.element.name]),
    ("parameters", sorted ((plan.params.map fun param => if param.calldata then "calldata" else "memory") ++
      (if plan.params.length = 2 then ["two"] else []))),
    ("lengths", sorted (plan.params.map fun param => match param.length with
      | .literal _ => "literal"
      | .input .. => "input")),
    ("elements", sorted (plan.params.map fun param => if param.raw then "raw" else "clean")),
    ("values", sorted (plan.values.map fun value => if value.raw then "raw" else "clean")),
    ("results", [match plan.result with
      | .word => "word"
      | .array (.var _) => "array"
      | .array (.param _) => "parameter"
      | .copy _ => "copy"]),
    ("calldataReads", sorted plan.calldataReads),
    ("parameterWrites", sorted plan.parameterWrites),
    ("encodings", sorted (runs.filterMap fun (outcome, events) => match outcome with
      | .output _ => if plan.result == .word then none
          else some (if events.contains .normalized then "normalized" else "canonical")
      | _ => none)),
    ("outcomes", sorted (runs.map (outcomeName ·.1))),
    ("dirty", sorted (dirtySites runs))]

end Plan

/-- Every value of each `runtime-memory-arrays` shape dimension. -/
def memoryShapeInventory : List (String × List String) :=
  [("types", sorted (IntType.all.map (·.name))),
    ("declarations", sorted ["new", "literal", "alias", "copy", "helper", "slice-range", "slice-from", "slice-to",
      "slice-all", "tail", "grid-new", "grid-arrays", "grid-literal"]),
    ("writes", sorted (["plain", "put", "inc", "fill", "set-row"] ++
      Op.all.flatMap fun op => [op.name, "unchecked-" ++ op.name])),
    ("targets", ["array", "row", "storage"]),
    ("members", ["pop", "push", "set-length"]),
    ("observations", sorted ["length", "element", "grid-length", "sum", "get", "len"]),
    ("collections", ["array", "row", "slice", "storage"]),
    ("bases", ["array", "row", "slice", "storage"]),
    ("indices", ["counter", "flagged", "input", "literal"]),
    ("lengths", ["flagged", "input", "literal"]),
    ("loops", ["array", "row", "slice", "storage"]),
    ("sharing", ["alias", "copy", "row", "view"]),
    ("outcomes", ["panic-0x11", "panic-0x12", "panic-0x31", "panic-0x32", "panic-0x41", "returned"]),
    ("panics", sorted ["read", "write", "row", "slice-start", "slice-end", "slice-read", "stale", "pop", "new",
      "grid-new", "compound-overflow", "compound-zero", "inc", "sum"])]

/-- Every value of each `runtime-array-abi` shape dimension. -/
def abiShapeInventory : List (String × List String) :=
  [("types", sorted (IntType.all.map (·.name))),
    ("parameters", ["calldata", "memory", "two"]),
    ("lengths", ["input", "literal"]),
    ("elements", ["clean", "raw"]),
    ("values", ["clean", "raw"]),
    ("results", ["array", "copy", "parameter", "word"]),
    ("calldataReads", sorted ["length", "element", "get", "slice", "copy", "loop"]),
    ("parameterWrites", ["compound", "fill", "memref", "plain"]),
    ("encodings", ["canonical", "normalized"]),
    ("outcomes", ["dirty", "panic-0x11", "panic-0x12", "panic-0x32", "panic-0x41", "returned"]),
    ("dirty", ["copy", "memory", "read"])]

/-! Fitting. -/

namespace Plan

/-- A result naming a dropped array or slice falls back to the fold, whose
values are then converted. -/
def withSteps (plan : Plan) (steps : List Step) : Plan :=
  let arrays := (steps.filter fun step => match step with
    | .alloc _ | .literal _ | .alias _ | .copy _ | .made .. => true
    | _ => false).length
  let slices := (steps.filter fun step => match step with
    | .slice .. | .tail .. => true
    | _ => false).length
  let result := match plan.result with
    | .array (.var index) => if index < arrays then plan.result else .word
    | .copy index => if index < slices then plan.result else .word
    | other => other
  let values := if result == .word then plan.values.map ({· with raw := false}) else plan.values
  {plan with steps, result, values}

/-- Steps are dropped from the end while the reference exceeds the budget and
more than one step remains. -/
def fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range maximumSteps do
    if plan.nodes > nodes && plan.steps.length > 1 then plan := plan.withSteps plan.steps.dropLast
  return plan

end Plan

/-! Generation: a SplitMix64 stream of the case seed, one domain per
profile. -/

def memoryDomain : UInt64 := 0x6d656d6172720001
def abiDomain : UInt64 := 0x6172726162690001

def indexLiterals : List Nat := [0, 1, 2, 3, 7]

/-- One to three values, the first at offset 0, each raw half the time when
`raw`. -/
def drawValues (type : IntType) (raw : Bool) : Gen (List ValueInput) := do
  let count := 1 + (← draw 3)
  let mut values : List ValueInput := []
  for position in List.range count do
    let offset ← if position = 0 then pure 0
      else do pure (type.offsets.getD (1 + (← draw (type.offsets.length - 1))) 0)
    let rawValue := raw && (← draw 2) == 0
    values := values ++ [{offset, raw := rawValue}]
  return values

/-- Zero to three indices weighted 1, 3, 3 and 2, a quarter of them flagged. -/
def drawIndices : Gen (List IndexInput) := do
  let mut indices : List IndexInput := []
  for _ in List.range (← drawWeighted [1, 3, 3, 2]) do
    let flagged := (← draw 4) == 0
    let shift := indexShifts.getD (← draw indexShifts.length) 0
    let mask := indexMasks.getD (← draw indexMasks.length) 1
    indices := indices ++ [{shift := if flagged then 0 else shift, mask, flagged}]
  return indices

/-- What exists while a plan is drawn. -/
structure Drawing where
  plan : Plan
  scope : Scope := {}
  storage : Bool
  loopDrawn : Bool := false
  raw : Bool := false

namespace Drawing

def names (drawing : Drawing) : List Name :=
  (List.range drawing.scope.arrays.length).map Name.var ++
    (drawing.plan.params.zipIdx.filterMap fun (param, index) => if param.calldata then none else some (Name.param index))

def calldata (drawing : Drawing) : List Nat :=
  drawing.plan.params.zipIdx.filterMap fun (param, index) => if param.calldata then some index else none

def pick {α : Type} [Inhabited α] (items : List α) : Gen α := do return items.getD (← draw items.length) default

/-- The grids whose rows can hold an element. -/
def rows (drawing : Drawing) : List Nat :=
  drawing.scope.grids.zipIdx.filterMap fun (info, index) => if 0 < info.rows then some index else none

/-- An index into a collection of at most `bound` elements: a literal inside
it nine times in ten and otherwise at or just past it, an index variable, or
in the loop the counter. -/
def index (drawing : Drawing) (inLoop : Bool) (bound : Nat) : Gen Index := do
  let indices := drawing.plan.indices.length
  match ← drawWeighted [3, if indices = 0 then 0 else 3, if inLoop then 4 else 0] with
  | 0 =>
      if 0 < bound && (← draw 10) != 0 then return .literal (← draw bound)
      else return .literal (min maximumIndexLiteral (bound + (← draw 2)))
  | 1 => return .input (← draw indices)
  | _ => return .counter

/-- A slice bound of a base of at most `bound` elements: a literal up to it
nine times in ten, otherwise just past it, or an index variable. -/
def bound (drawing : Drawing) (bound : Nat) : Gen Index := do
  let indices := drawing.plan.indices.length
  if indices = 0 || (← draw 2) == 0 then
    if (← draw 10) != 0 then return .literal (← draw (bound + 1))
    else return .literal (min maximumIndexLiteral (bound + 1))
  else return .input (← draw indices)

def collBound (drawing : Drawing) (inLoop : Bool) (coll : Coll) : Nat :=
  (drawing.scope.collBound? drawing.plan drawing.storage inLoop coll).getD 0

def gridBound (drawing : Drawing) (grid : Nat) : Nat := ((drawing.scope.grids[grid]?).map (·.bound)).getD 0

def value (drawing : Drawing) : Gen Value := do
  if (← draw 4) == 0 then return .literal (← draw drawing.plan.element.literals.length)
  else return .input (← draw drawing.plan.values.length)

/-- A literal length 0 to 4, or an index variable, flagged ones only where
`flagged`. -/
def length (drawing : Drawing) (flagged : Bool) : Gen Length := do
  let inputs := drawing.plan.indices.zipIdx.filterMap fun (input, index) =>
    if input.flagged && !flagged then none else some index
  if inputs.isEmpty || (← draw 3) == 0 then
    let zero := (← draw 8) == 0
    let size := 1 + (← draw maximumLiteral)
    return .literal (if zero then 0 else size)
  else return .input (← pick inputs)

def coll (drawing : Drawing) (inLoop : Bool) : Gen Coll := do
  let names := drawing.names
  let scope := drawing.scope
  match ← drawWeighted [if names.isEmpty then 0 else 3, if scope.slices.isEmpty then 0 else 2,
      if drawing.storage && 0 < scope.storage then 2 else 0, if drawing.rows.isEmpty then 0 else 2,
      if drawing.calldata.isEmpty then 0 else 3] with
  | 0 => return .array (← pick names)
  | 1 => return .slice (← draw scope.slices.length)
  | 2 => return .storage
  | 3 =>
      let grid ← pick drawing.rows
      return .row grid (← drawing.index inLoop (drawing.gridBound grid))
  | _ => return .calldata (← pick drawing.calldata)

def target (drawing : Drawing) (inLoop : Bool) : Gen Target := do
  let names := drawing.names
  match ← drawWeighted [if names.isEmpty then 0 else 4, if drawing.storage && 0 < drawing.scope.storage then 2 else 0,
      if drawing.rows.isEmpty then 0 else 2] with
  | 0 => return .array (← pick names)
  | 1 => return .storage
  | _ =>
      let grid ← pick drawing.rows
      return .row grid (← drawing.index inLoop (drawing.gridBound grid))

/-- Without element additions when the plan has raw values. -/
def form (drawing : Drawing) : Gen Form := do
  match ← drawWeighted [3, if drawing.raw then 0 else 3, 1, if drawing.raw then 0 else 1] with
  | 0 => return .plain
  | 1 => return .compound (← pick Op.all) ((← draw 3) == 0)
  | 2 => return .put
  | _ => return .inc

def cut (drawing : Drawing) (size : Nat) : Gen Cut := do
  match ← drawWeighted [2, 1, 1, 1] with
  | 0 =>
      let first ← drawing.bound size
      let last ← drawing.bound size
      return match first, last with
        | .literal start, .literal stop => if stop < start then .range last first else .range first last
        | _, _ => .range first last
  | 1 => return .start (← drawing.bound size)
  | 2 => return .stop (← drawing.bound size)
  | _ => return .all

def observation (drawing : Drawing) (inLoop : Bool) : Gen Observation := do
  let names := drawing.names
  match ← drawWeighted [2, 4, if drawing.scope.grids.isEmpty then 0 else 1,
      if names.isEmpty || drawing.raw then 0 else 1, 1, 1] with
  | 0 => return .length (← drawing.coll inLoop)
  | 1 =>
      let coll ← drawing.coll inLoop
      return .element coll (← drawing.index inLoop (drawing.collBound inLoop coll))
  | 2 => return .gridLength (← draw drawing.scope.grids.length)
  | 3 => return .sum (← pick names)
  | 4 =>
      let coll ← drawing.coll inLoop
      return .get coll (← drawing.index inLoop (drawing.collBound inLoop coll))
  | _ => return .len (← drawing.coll inLoop)

def action (drawing : Drawing) (inLoop : Bool) (write : Bool) : Gen Action := do
  if write then
    let target ← drawing.target inLoop
    let size := (drawing.scope.targetBound? drawing.plan drawing.storage inLoop target).getD 0
    return .write target (← drawing.index inLoop size) (← drawing.value) (← drawing.form)
  else return .observe (← drawing.observation inLoop)

/-- A step of a kind whose operands exist, by weight. -/
def step (drawing : Drawing) : Gen Step := do
  let names := drawing.names
  let scope := drawing.scope
  let arrays := scope.arrays.length < maximumArrays
  let slices := scope.slices.length < maximumSlices
  let grids := scope.grids.length < maximumGrids
  let stored := drawing.storage && 0 < scope.storage
  let viewed := scope.slices.any (·.storage)
  let collections := !names.isEmpty || !scope.slices.isEmpty || stored || !drawing.rows.isEmpty ||
    !drawing.calldata.isEmpty
  let targets := !names.isEmpty || stored || !drawing.rows.isEmpty
  let weights := [if arrays then 3 else 0, if arrays then 3 else 0, if arrays && !names.isEmpty then 1 else 0,
    if arrays && !scope.slices.isEmpty then 1 else 0, if arrays then 1 else 0,
    if slices && collections then 3 else 0, if slices && !names.isEmpty then 1 else 0,
    if grids then 1 else 0, if grids && !names.isEmpty then 1 else 0, if grids then 1 else 0,
    if !scope.grids.isEmpty && !names.isEmpty then 1 else 0, if targets then 4 else 0,
    if names.isEmpty then 0 else 1, if drawing.storage && scope.storage < maximumBound then 2 else 0,
    if drawing.storage && 0 < scope.storage then (if viewed then 4 else 1) else 0,
    if drawing.storage then (if viewed then 3 else 1) else 0, if collections then 5 else 0,
    if collections && !drawing.loopDrawn then 2 else 0]
  match ← drawWeighted weights with
  | 0 => return .alloc (← drawing.length true)
  | 1 =>
      let mut values := []
      for _ in List.range (1 + (← draw maximumLiteral)) do values := values ++ [← drawing.value]
      return .literal values
  | 2 => return .alias (← pick names)
  | 3 => return .copy (← draw scope.slices.length)
  | 4 => return .made (← drawing.value) (← drawing.value)
  | 5 =>
      let base ← drawing.coll false
      return .slice base (← drawing.cut (drawing.collBound false base))
  | 6 =>
      let source ← pick names
      return .tail source (← drawing.bound ((scope.nameBound? drawing.plan source).getD 0))
  | 7 => return .grid (← drawing.length true)
  | 8 =>
      let mut sources := []
      for _ in List.range (1 + (← draw maximumRows)) do sources := sources ++ [← pick names]
      return .gridOf sources
  | 9 =>
      let mut rows := []
      for _ in List.range (1 + (← draw maximumRows)) do
        let mut row := []
        for _ in List.range (1 + (← draw maximumRows)) do row := row ++ [← drawing.value]
        rows := rows ++ [row]
      return .gridLiteral rows
  | 10 =>
      let grid ← draw scope.grids.length
      return .setRow grid (← drawing.index false (drawing.gridBound grid)) (← pick names)
  | 11 => return .act (← drawing.action false true)
  | 12 => return .fill (← pick names) (← drawing.value)
  | 13 => return .push (← drawing.value)
  | 14 => return .pop
  | 15 => return .setLength (← drawing.length false)
  | 16 => return .act (← drawing.action false false)
  | _ =>
      let over ← drawing.coll false
      let mut body := []
      for _ in List.range (1 + (← draw maximumBody)) do body := body ++ [← drawing.action true ((← draw 2) == 0)]
      return .loop over body

/-- Draw `count` steps, each admitted by the scope or drawn again, up to four
times; the last is an observation when none was drawn before. -/
def steps (drawing : Drawing) (count : Nat) : Gen (List Step × Scope) := do
  let mut drawing := drawing
  let mut steps : List Step := []
  for position in List.range count do
    let mut chosen : Option (Step × Scope) := none
    for _ in List.range 4 do
      if chosen.isNone then
        let candidate ← if position + 1 = count && !steps.any (fun step => step.actions.any (·.observes)) then
            do pure (Step.act (← drawing.action false false))
          else drawing.step
        let plan := {drawing.plan with steps := steps}
        if let some next := drawing.scope.step? plan drawing.storage candidate then chosen := some (candidate, next)
    if let some (step, next) := chosen then
      steps := steps ++ [step]
      drawing := {drawing with scope := next, loopDrawn := drawing.loopDrawn || step.isLoop}
  return (steps, drawing.scope)

end Drawing

/-- A `runtime-memory-arrays` plan: an element type, one to three values,
zero to three indices and three to ten steps over the storage array too. -/
def drawMemory : Gen Plan := do
  let element ← Drawing.pick IntType.all
  let values ← drawValues element false
  let indices ← drawIndices
  let plan : Plan := {element, values, indices, params := [], steps := [], result := .word}
  let (steps, _) ← ({plan, storage := true} : Drawing).steps (3 + (← draw 8))
  return {plan with steps}

/-- A `runtime-array-abi` plan: an element type, one parameter, or two a
third of the time, each memory or calldata evenly, a literal or an input
length evenly and raw half the time for a narrow type; the result a fold,
an array or a copy evenly, raw values half the time for an array result;
then zero to three indices and two to eight steps. -/
def drawAbi : Gen Plan := do
  let element ← Drawing.pick IntType.all
  let narrow := element.bytes < 32
  let mut params : List Param := []
  for _ in List.range (if (← draw 3) == 0 then 2 else 1) do
    let calldata := (← draw 2) == 0
    let length ← if (← draw 2) == 0 then do
        let zero := (← draw 8) == 0
        let size := 1 + (← draw maximumLiteral)
        pure (ParamLength.literal (if zero then 0 else size))
      else do pure (ParamLength.input (← Drawing.pick indexShifts) (← Drawing.pick indexMasks))
    let offset ← Drawing.pick element.offsets
    params := params ++ [{calldata, length, offset, raw := narrow && (← draw 2) == 0}]
  let kind ← draw 3
  let values ← drawValues element (narrow && kind != 0)
  let indices ← drawIndices
  let plan : Plan := {element, values, indices, params, steps := [], result := .word}
  let raw := values.any (·.raw)
  let (steps, scope) ← ({plan, storage := false, raw} : Drawing).steps (2 + (← draw 7))
  let names := ({plan, storage := false, scope} : Drawing).names
  let array : Gen Result := do
    if names.isEmpty then return .word else return .array (← Drawing.pick names)
  let result ← match kind with
    | 0 => pure Result.word
    | 1 => array
    | _ => do
        if scope.slices.isEmpty then array else pure (Result.copy (← draw scope.slices.length))
  let values := if result == .word then values.map ({· with raw := false}) else values
  return {plan with values, steps, result}

def generateMemory (seed : UInt64) : Plan :=
  Id.run (drawMemory.run' {seed, domain := memoryDomain, index := 0})

def generateAbi (seed : UInt64) : Plan :=
  Id.run (drawAbi.run' {seed, domain := abiDomain, index := 0})

end Solcore.Synthesis.Core.Arrays
end

section
-- leanmerge: from Solcore.Synthesis.Core.ArraysShrink
/-! Plan size and reductions of the array plans. Every candidate is strictly
smaller in `Plan.size` and must still be admitted by its profile and pass the
full Core checker; that sealing is the cases module's. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Arrays

open Solcore.Synthesis.Core.Integers (IntType Op)

/-! Weights: a literal 0 index, `sc_v0` and a literal 0 length weigh
nothing. -/

def Index.weight : Index → Nat
  | .literal value => value
  | .input index => 8 + index
  | .counter => 8

def Value.weight : Value → Nat
  | .input index => index
  | .literal index => 3 + index

def Length.weight : Length → Nat
  | .literal value => value
  | .input index => 5 + index

def Name.weight : Name → Nat
  | .var index | .param index => index

def Coll.weight : Coll → Nat
  | .array name => 1 + name.weight
  | .slice index => 2 + index
  | .storage => 2
  | .row grid index => 3 + grid + index.weight
  | .calldata index => 1 + index

def Target.weight : Target → Nat
  | .array name => 1 + name.weight
  | .storage => 2
  | .row grid index => 3 + grid + index.weight

def opWeight : Op → Nat
  | .add => 0
  | .sub => 1
  | .mul => 2
  | .div => 3
  | .mod => 4

def Form.weight : Form → Nat
  | .plain => 0
  | .put => 1
  | .compound op unchecked => 2 + opWeight op + (if unchecked then 1 else 0)
  | .inc => 2

def Cut.weight : Cut → Nat
  | .all => 0
  | .start first => 1 + first.weight
  | .stop last => 1 + last.weight
  | .range first last => 2 + first.weight + last.weight

def Observation.weight : Observation → Nat
  | .length coll => 1 + coll.weight
  | .element coll index => 2 + coll.weight + index.weight
  | .gridLength grid => 1 + grid
  | .sum name => 3 + name.weight
  | .get coll index => 3 + coll.weight + index.weight
  | .len coll => 2 + coll.weight

def Action.weight : Action → Nat
  | .write target index value form => 2 + target.weight + index.weight + value.weight + form.weight
  | .observe observation => 1 + observation.weight

def Step.weight : Step → Nat
  | .alloc length => 2 + length.weight
  | .literal values => 1 + (values.map (1 + ·.weight)).foldl (· + ·) 0
  | .alias source => 2 + source.weight
  | .copy number => 3 + number
  | .made left right => 4 + left.weight + right.weight
  | .slice base cut => 3 + base.weight + cut.weight
  | .tail source start => 5 + source.weight + start.weight
  | .grid length => 3 + length.weight
  | .gridOf sources => 3 + (sources.map (1 + ·.weight)).foldl (· + ·) 0
  | .gridLiteral rows => 4 + (rows.map fun row => 1 + (row.map (1 + ·.weight)).foldl (· + ·) 0).foldl (· + ·) 0
  | .setRow which index source => 3 + which + index.weight + source.weight
  | .act action => action.weight
  | .fill target value => 3 + target.weight + value.weight
  | .push value => 2 + value.weight
  | .pop => 2
  | .setLength length => 2 + length.weight
  | .loop over body => 4 + over.weight + (body.map (1 + ·.weight)).foldl (· + ·) 0

def ParamLength.weight : ParamLength → Nat
  | .literal value => value
  | .input .. => 5

namespace Plan

def offsetWeight (plan : Plan) (offset : Nat) : Nat := (plan.element.offsets.idxOf? offset).getD 0

def resultWeight : Result → Nat
  | .word => 0
  | .array name => 1 + name.weight
  | .copy slice => 2 + slice

/-- The plan size: every step's weight, each value, index and parameter, and
the result. -/
def size (plan : Plan) : Nat :=
  (plan.steps.map (·.weight)).foldl (· + ·) 0 +
    (plan.values.map fun value => 1 + plan.offsetWeight value.offset + (if value.raw then 1 else 0)).foldl (· + ·) 0 +
    (plan.indices.map fun index => 1 + (indexShifts.idxOf? index.shift).getD 0 + (indexMasks.idxOf? index.mask).getD 0 +
      (if index.flagged then 2 else 0)).foldl (· + ·) 0 +
    (plan.params.map fun param => 1 + (if param.calldata then 1 else 0) + param.length.weight +
      plan.offsetWeight param.offset + (if param.raw then 1 else 0)).foldl (· + ·) 0 +
    resultWeight plan.result

end Plan

/-! Removing a declaration renumbers the later names of its kind. -/

/-- What a step declares: an array, a slice or a grid. -/
inductive Declared where
  | array
  | slice
  | grid
  | none
  deriving BEq

def Step.declared : Step → Declared
  | .alloc _ | .literal _ | .alias _ | .copy _ | .made .. => .array
  | .slice .. | .tail .. => .slice
  | .grid _ | .gridOf _ | .gridLiteral _ => .grid
  | _ => .none

/-- The names a step reads. -/
structure Uses where
  arrays : List Nat := []
  slices : List Nat := []
  grids : List Nat := []

def Name.uses : Name → Uses
  | .var index => {arrays := [index]}
  | .param _ => {}

def Uses.join (left right : Uses) : Uses :=
  {arrays := left.arrays ++ right.arrays, slices := left.slices ++ right.slices, grids := left.grids ++ right.grids}

def Coll.uses : Coll → Uses
  | .array name => name.uses
  | .slice index => {slices := [index]}
  | .row grid _ => {grids := [grid]}
  | _ => {}

def Target.uses : Target → Uses
  | .array name => name.uses
  | .row grid _ => {grids := [grid]}
  | .storage => {}

def Observation.uses : Observation → Uses
  | .length coll | .element coll _ | .get coll _ | .len coll => coll.uses
  | .gridLength grid => {grids := [grid]}
  | .sum name => name.uses

def Action.uses : Action → Uses
  | .write target _ _ _ => target.uses
  | .observe observation => observation.uses

def Step.uses : Step → Uses
  | .alias source | .tail source _ | .fill source _ => source.uses
  | .copy number => {slices := [number]}
  | .slice base _ => base.uses
  | .gridOf sources => sources.foldl (fun uses source => uses.join source.uses) {}
  | .setRow which _ source => ({grids := [which]} : Uses).join source.uses
  | .act action => action.uses
  | .loop over body => body.foldl (fun uses action => uses.join action.uses) over.uses
  | _ => {}

/-- Renumber a name of each kind after the removed ones. -/
structure Renumber where
  arrays : List Nat
  slices : List Nat
  grids : List Nat

def Renumber.shift (removed : List Nat) (index : Nat) : Nat := index - (removed.filter (· < index)).length

namespace Renumber

def name (renumber : Renumber) : Name → Name
  | .var index => .var (shift renumber.arrays index)
  | other => other

def coll (renumber : Renumber) : Coll → Coll
  | .array name => .array (renumber.name name)
  | .slice index => .slice (shift renumber.slices index)
  | .row grid index => .row (shift renumber.grids grid) index
  | other => other

def target (renumber : Renumber) : Target → Target
  | .array name => .array (renumber.name name)
  | .row grid index => .row (shift renumber.grids grid) index
  | .storage => .storage

def observation (renumber : Renumber) : Observation → Observation
  | .length coll => .length (renumber.coll coll)
  | .element coll index => .element (renumber.coll coll) index
  | .gridLength grid => .gridLength (shift renumber.grids grid)
  | .sum name => .sum (renumber.name name)
  | .get coll index => .get (renumber.coll coll) index
  | .len coll => .len (renumber.coll coll)

def action (renumber : Renumber) : Action → Action
  | .write target index value form => .write (renumber.target target) index value form
  | .observe observation => .observe (renumber.observation observation)

def step (renumber : Renumber) : Step → Step
  | .alias source => .alias (renumber.name source)
  | .copy slice => .copy (shift renumber.slices slice)
  | .slice base cut => .slice (renumber.coll base) cut
  | .tail source start => .tail (renumber.name source) start
  | .gridOf sources => .gridOf (sources.map renumber.name)
  | .setRow grid index source => .setRow (shift renumber.grids grid) index (renumber.name source)
  | .act action => .act (renumber.action action)
  | .fill target value => .fill (renumber.name target) value
  | .loop over body => .loop (renumber.coll over) (body.map renumber.action)
  | other => other

end Renumber

namespace Plan

/-- The step at `index` removed with every later step that reads what a
removed step declared; the later names renumbered, and a result naming a
removed array or slice becomes the fold. -/
def removeStep (plan : Plan) (index : Nat) : Plan := Id.run do
  let mut arrays := 0
  let mut slices := 0
  let mut grids := 0
  let mut removed : Renumber := {arrays := [], slices := [], grids := []}
  let mut kept : List Step := []
  for (step, position) in plan.steps.zipIdx do
    let uses := step.uses
    let drop := position = index || uses.arrays.any removed.arrays.contains ||
      uses.slices.any removed.slices.contains || uses.grids.any removed.grids.contains
    match step.declared with
    | .array => if drop then removed := {removed with arrays := removed.arrays ++ [arrays]}
                arrays := arrays + 1
    | .slice => if drop then removed := {removed with slices := removed.slices ++ [slices]}
                slices := slices + 1
    | .grid => if drop then removed := {removed with grids := removed.grids ++ [grids]}
               grids := grids + 1
    | .none => pure ()
    if !drop then kept := kept ++ [removed.step step]
  let result := match plan.result with
    | .array (.var array) => if removed.arrays.contains array then .word else .array (.var (Renumber.shift removed.arrays array))
    | .copy slice => if removed.slices.contains slice then .word else .copy (Renumber.shift removed.slices slice)
    | other => other
  let values := if result == .word then plan.values.map ({· with raw := false}) else plan.values
  return {plan with steps := kept, result, values}

def replaceStep (plan : Plan) (index : Nat) (step : Step) : Plan := {plan with steps := plan.steps.set index step}

end Plan

/-! Lowered operands and forms. -/

def Index.lowered : Index → List Index
  | .literal 0 => []
  | _ => [.literal 0]

def Value.lowered : Value → List Value
  | .input 0 => []
  | _ => [.input 0]

def Length.lowered : Length → List Length
  | .literal 0 => []
  | _ => [.literal 0]

def Form.lowered : Form → List Form
  | .plain => []
  | .put | .inc => [.plain]
  | .compound op unchecked =>
      [.plain] ++ (if unchecked then [.compound op false] else []) ++ (if op == .add then [] else [.compound .add unchecked])

def Coll.lowered : Coll → List Coll
  | .row grid index => index.lowered.map (.row grid ·)
  | _ => []

def Target.lowered : Target → List Target
  | .row grid index => index.lowered.map (.row grid ·)
  | _ => []

def Observation.lowered : Observation → List Observation
  | .length coll => coll.lowered.map .length
  | .element coll index => [.length coll] ++ coll.lowered.map (.element · index) ++ index.lowered.map (.element coll ·)
  | .gridLength _ => []
  | .sum name => [.length (.array name)]
  | .get coll index => [.element coll index] ++ index.lowered.map (.get coll ·)
  | .len coll => [.length coll]

/-- The loop's counter read as the literal 0, for its body run once. -/
def Index.once : Index → Index
  | .counter => .literal 0
  | other => other

def Coll.once : Coll → Coll
  | .row grid index => .row grid index.once
  | other => other

def Target.once : Target → Target
  | .row grid index => .row grid index.once
  | other => other

def Observation.once : Observation → Observation
  | .length coll => .length coll.once
  | .element coll index => .element coll.once index.once
  | .get coll index => .get coll.once index.once
  | .len coll => .len coll.once
  | other => other

def Action.once : Action → Action
  | .write target index value form => .write target.once index.once value form
  | .observe observation => .observe observation.once

def Action.lowered : Action → List Action
  | .write target index value form =>
      (form.lowered.map (.write target index value ·)) ++ (target.lowered.map (.write · index value form)) ++
        (index.lowered.map (.write target · value form)) ++ (value.lowered.map (.write target index · form))
  | .observe observation => observation.lowered.map .observe

def Cut.lowered : Cut → List Cut
  | .all => []
  | .range first last => [.all] ++ first.lowered.map (.range · last) ++ last.lowered.map (.range first ·)
  | .start first => [.all] ++ first.lowered.map .start
  | .stop last => [.all] ++ last.lowered.map .stop

def dropLast {α : Type} (items : List α) : List (List α) := if items.length ≥ 2 then [items.dropLast] else []

/-- The simpler forms of one step. -/
def Step.lowered : Step → List Step
  | .alloc length => length.lowered.map .alloc
  | .literal values => (dropLast values).map .literal ++
      (List.range values.length).flatMap fun position =>
        ((values.getD position default).lowered.map fun value => .literal (values.set position value))
  | .made left right => [.literal [left, right]] ++ left.lowered.map (.made · right) ++ right.lowered.map (.made left ·)
  | .slice base cut => cut.lowered.map (.slice base ·) ++ base.lowered.map (.slice · cut)
  | .tail source start => [.slice (.array source) (.start start)] ++ start.lowered.map (.tail source ·)
  | .grid length => length.lowered.map .grid
  | .gridOf sources => [.grid (.literal 0)] ++ (dropLast sources).map .gridOf
  | .gridLiteral rows => [.grid (.literal 0)] ++ (dropLast rows).map .gridLiteral ++
      (List.range rows.length).flatMap fun position => (dropLast (rows.getD position [])).map fun row =>
        .gridLiteral (rows.set position row)
  | .setRow which index source => index.lowered.map (.setRow which · source)
  | .act action => action.lowered.map .act
  | .fill target value => value.lowered.map (.fill target ·)
  | .push value => value.lowered.map .push
  | .setLength length => length.lowered.map .setLength
  | .loop over body => (dropLast body).map (.loop over ·) ++
      (List.range body.length).flatMap fun position =>
        (body.getD position default).lowered.map fun action => .loop over (body.set position action)
  | _ => []

namespace Plan

/-- The loop at `index` replaced by its body run once, at counter 0. -/
def unrollLoop (plan : Plan) (index : Nat) : Option Plan :=
  match plan.steps[index]? with
  | some (.loop _ body) =>
      some {plan with steps := (plan.steps.take index) ++ body.map (Step.act ∘ Action.once) ++ plan.steps.drop (index + 1)}
  | _ => none

def stepReductions (plan : Plan) : List Plan :=
  (List.range plan.steps.length).flatMap fun index =>
    [plan.removeStep index] ++ (plan.unrollLoop index).toList ++
      ((plan.steps.getD index default).lowered.map (plan.replaceStep index ·))

/-- The last value or index input removed, its references reading `sc_v0`
or the literal 0; a flagged index masked; the second parameter removed with
the steps that read it; a parameter's length a literal 0 and its elements
clean; an array result the fold. -/
def inputReductions (plan : Plan) : List Plan :=
  let lastValue := plan.values.length - 1
  let valueRef : Value → Value
    | .input index => if index = lastValue then .input 0 else .input index
    | other => other
  let lastIndex := plan.indices.length - 1
  let indexRef : Index → Index
    | .input index => if index = lastIndex then .literal 0 else .input index
    | other => other
  let lengthRef : Length → Length
    | .input index => if index = lastIndex then .literal 0 else .input index
    | other => other
  let mapStep (index : Index → Index) (value : Value → Value) (length : Length → Length) : Step → Step :=
    let coll : Coll → Coll
      | .row grid row => .row grid (index row)
      | other => other
    let target : Target → Target
      | .row grid row => .row grid (index row)
      | other => other
    let observation : Observation → Observation
      | .length c => .length (coll c)
      | .element c i => .element (coll c) (index i)
      | .get c i => .get (coll c) (index i)
      | .len c => .len (coll c)
      | other => other
    let action : Action → Action
      | .write t i v f => .write (target t) (index i) (value v) f
      | .observe o => .observe (observation o)
    let cut : Cut → Cut
      | .range s e => .range (index s) (index e)
      | .start s => .start (index s)
      | .stop e => .stop (index e)
      | .all => .all
    fun
      | .alloc l => .alloc (length l)
      | .literal values => .literal (values.map value)
      | .made l r => .made (value l) (value r)
      | .slice base c => .slice (coll base) (cut c)
      | .tail source start => .tail source (index start)
      | .grid l => .grid (length l)
      | .gridLiteral rows => .gridLiteral (rows.map (·.map value))
      | .setRow grid i source => .setRow grid (index i) source
      | .act a => .act (action a)
      | .fill t v => .fill t (value v)
      | .push v => .push (value v)
      | .setLength l => .setLength (length l)
      | .loop over body => .loop (coll over) (body.map action)
      | other => other
  let removeValue := if plan.values.length ≥ 2 then
      [{plan with values := plan.values.dropLast, steps := plan.steps.map (mapStep id valueRef id)}] else []
  let removeIndex := if plan.indices.isEmpty then [] else
      [{plan with indices := plan.indices.dropLast, steps := plan.steps.map (mapStep indexRef id lengthRef)}]
  let unflag := (List.range plan.indices.length).filterMap fun position =>
    let input := plan.indices.getD position default
    if input.flagged then some {plan with indices := plan.indices.set position {input with flagged := false}} else none
  let clean := (List.range plan.values.length).filterMap fun position =>
    let input := plan.values.getD position default
    if input.raw then some {plan with values := plan.values.set position {input with raw := false}} else none
  let second := if plan.params.length = 2 then
      let uses (step : Step) : Bool := match step with
        | .slice (.calldata 1) _ | .slice (.array (.param 1)) _ | .loop (.calldata 1) _ | .loop (.array (.param 1)) _ => true
        | .alias (.param 1) | .tail (.param 1) _ | .fill (.param 1) _ | .setRow _ _ (.param 1) => true
        | .gridOf sources => sources.contains (.param 1)
        | _ => step.actions.any fun action => match action with
            | .write (.array (.param 1)) _ _ _ => true
            | .observe (.sum (.param 1)) => true
            | .observe observation => (observation.coll?.map fun coll => coll == .calldata 1 || coll == .array (.param 1)).getD false
            | _ => false
      let kept := {plan with params := plan.params.take 1, steps := plan.steps.filter (!uses ·)}
      [if plan.result == .array (.param 1) then {kept with result := .word, values := kept.values.map ({· with raw := false})}
        else kept]
    else []
  let params := (List.range plan.params.length).flatMap fun position =>
    let param := plan.params.getD position default
    (if param.length matches .literal 0 then [] else [{plan with params := plan.params.set position {param with length := .literal 0}}]) ++
      (if param.raw then [{plan with params := plan.params.set position {param with raw := false}}] else [])
  let result := if plan.result == .word then [] else [{plan with result := .word, values := plan.values.map ({· with raw := false})}]
  removeValue ++ removeIndex ++ unflag ++ clean ++ second ++ params ++ result

/-- Every reduction of the plan. -/
def reductions (plan : Plan) : List Plan := plan.stepReductions ++ plan.inputReductions

end Plan

end Solcore.Synthesis.Core.Arrays
end

section
-- leanmerge: from Solcore.Synthesis.Source.ArraysEmitter
/-! The Solcore source of an array plan: the helpers it uses, then
`SynthesizedMemoryArrays.run(uint256)`, with the storage array `sc_st` when
the plan uses it, or `SynthesizedArrayAbi.run` with its `T[]` and
`calldata<T[]>` parameters, which converts the input Word to its values and
indices, runs the steps and folds every observation into `sc_r`, then
returns it or a `T[]`. The source is a function of the plan; nothing here
builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Arrays

open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Core.Integers (IntType Op)
open Solcore.Synthesis.Source.Integers (convertText intText hexText opSymbol)

def memoryEmitterVersion : String := "solcore-source-memory-arrays-v1"
def memoryWrapperVersion : String := "solcore-memory-arrays-contract-v1"
def memoryContract : String := "SynthesizedMemoryArrays"
def abiEmitterVersion : String := "solcore-source-array-abi-v1"
def abiWrapperVersion : String := "solcore-array-abi-contract-v1"
def abiContract : String := "SynthesizedArrayAbi"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def offsetText (offset : Nat) : String := if offset = 0 then "sc_x" else "(sc_x + " ++ toString offset ++ ")"

def valueDeclaration (type : IntType) (input : ValueInput) (index : Nat) : String :=
  "let sc_v" ++ toString index ++ ": " ++ type.name ++ " = Typedef.abs(" ++
    (if input.raw then offsetText input.offset else convertText type (offsetText input.offset)) ++ ");"

def indexDeclaration (input : IndexInput) (index : Nat) : String :=
  let word := if input.flagged then "(sc_x & " ++ hexText (flag + input.mask) ++ ")"
    else if input.shift = 0 then "(sc_x & " ++ toString input.mask ++ ")"
    else "((sc_x >> " ++ toString input.shift ++ ") & " ++ toString input.mask ++ ")"
  "let sc_k" ++ toString index ++ ": uint256 = uint256(" ++ word ++ ");"

def indexText : Index → String
  | .literal value => toString value
  | .input index => "sc_k" ++ toString index
  | .counter => "sc_i"

/-- A literal index of a slice or a calldata parameter is typed: upstream's
inference leaves `Typedef.rep(s[0])` ambiguous there. -/
def elementIndexText (coll : Coll) (index : Index) : String :=
  match coll, index with
  | .slice _, .literal value | .calldata _, .literal value => "uint256(" ++ toString value ++ ")"
  | _, _ => indexText index

def valueText (type : IntType) : Value → String
  | .input index => "sc_v" ++ toString index
  | .literal index => intText (type.literals.getD index 0)

def lengthText : Length → String
  | .literal value => toString value
  | .input index => "sc_k" ++ toString index

def nameText : Name → String
  | .var index => "sc_a" ++ toString index
  | .param index => "sc_p" ++ toString index

def collText : Coll → String
  | .array name => nameText name
  | .slice index => "sc_s" ++ toString index
  | .storage => "sc_st"
  | .row grid index => "sc_g" ++ toString grid ++ "[" ++ indexText index ++ "]"
  | .calldata index => "sc_p" ++ toString index

def targetText : Target → String
  | .array name => nameText name
  | .storage => "sc_st"
  | .row grid index => "sc_g" ++ toString grid ++ "[" ++ indexText index ++ "]"

def cutText : Cut → String
  | .range start stop => "[" ++ indexText start ++ ":" ++ indexText stop ++ "]"
  | .start start => "[" ++ indexText start ++ ":]"
  | .stop stop => "[:" ++ indexText stop ++ "]"
  | .all => "[:]"

def observationText : Observation → String
  | .length coll => collText coll ++ ".length"
  | .element coll index => collText coll ++ "[" ++ elementIndexText coll index ++ "]"
  | .gridLength grid => "sc_g" ++ toString grid ++ ".length"
  | .sum name => "sc_sum(" ++ nameText name ++ ")"
  | .get coll index => "sc_get(" ++ collText coll ++ ", " ++ indexText index ++ ")"
  | .len coll => "sc_len(" ++ collText coll ++ ")"

def actionLines (type : IntType) : Action → List String
  | .write target index value form =>
      let target := targetText target
      let index := indexText index
      let value := valueText type value
      match form with
      | .plain => [target ++ "[" ++ index ++ "] = " ++ value ++ ";"]
      | .compound op false => [target ++ "[" ++ index ++ "] " ++ opSymbol op ++ "= " ++ value ++ ";"]
      | .compound op true => ["unchecked {", "    " ++ target ++ "[" ++ index ++ "] " ++ opSymbol op ++ "= " ++ value ++ ";", "}"]
      | .put => ["sc_put(lidx(" ++ target ++ ", " ++ index ++ "), " ++ value ++ ");"]
      | .inc => ["sc_inc(lidx(" ++ target ++ ", " ++ index ++ "), " ++ value ++ ");"]
  | .observe observation =>
      ["sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(" ++ observationText observation ++ "));"]

/-- A step's statements; `arrays`, `slices` and `grids` count the names
declared before it. -/
def stepLines (type : IntType) (arrays slices grids : Nat) : Step → List String
  | .alloc length => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = new " ++ type.name ++ "[](" ++
      lengthText length ++ ");"]
  | .literal values => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = [" ++
      ", ".intercalate (values.map (valueText type)) ++ "];"]
  | .alias source => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = " ++ nameText source ++ ";"]
  | .copy slice => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = toArray(sc_s" ++ toString slice ++ ");"]
  | .made left right => ["let sc_a" ++ toString arrays ++ ": " ++ type.name ++ "[] = sc_mk(" ++ valueText type left ++
      ", " ++ valueText type right ++ ");"]
  | .slice base cut => ["let sc_s" ++ toString slices ++ " = " ++ collText base ++ cutText cut ++ ";"]
  | .tail source start => ["let sc_s" ++ toString slices ++ " = sc_tail(" ++ nameText source ++ ", " ++
      indexText start ++ ");"]
  | .grid length => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = new " ++ type.name ++ "[][](" ++
      lengthText length ++ ");"]
  | .gridOf sources => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = [" ++
      ", ".intercalate (sources.map nameText) ++ "];"]
  | .gridLiteral rows => ["let sc_g" ++ toString grids ++ ": " ++ type.name ++ "[][] = [" ++
      ", ".intercalate (rows.map fun row => "[" ++ ", ".intercalate (row.map (valueText type)) ++ "]") ++ "];"]
  | .setRow grid index source => ["sc_g" ++ toString grid ++ "[" ++ indexText index ++ "] = " ++ nameText source ++ ";"]
  | .act action => actionLines type action
  | .fill target value => ["sc_fill(" ++ nameText target ++ ", " ++ valueText type value ++ ");"]
  | .push value => ["sc_st.push(" ++ valueText type value ++ ");"]
  | .pop => ["sc_st.pop();"]
  | .setLength length => ["sc_st.setLength(" ++ lengthText length ++ ");"]
  | .loop over body =>
      ["for (let sc_i: uint256 = 0; sc_i < " ++ collText over ++ ".length; sc_i += 1) {"] ++
        indent 4 (body.flatMap (actionLines type)) ++ ["}"]

def stepsLines (plan : Plan) : List String := Id.run do
  let mut lines : List String := []
  let mut arrays := 0
  let mut slices := 0
  let mut grids := 0
  for step in plan.steps do
    lines := lines ++ stepLines plan.element arrays slices grids step
    match step with
    | .alloc _ | .literal _ | .alias _ | .copy _ | .made .. => arrays := arrays + 1
    | .slice .. | .tail .. => slices := slices + 1
    | .grid _ | .gridOf _ | .gridLiteral _ => grids := grids + 1
    | _ => pure ()
  return lines

def actions (plan : Plan) : List Action := plan.steps.flatMap (·.actions)

def unchecked (plan : Plan) : Bool := (actions plan).any fun
  | .write _ _ _ (.compound _ true) => true
  | _ => false

def uses (plan : Plan) (helper : String) : Bool :=
  match helper with
  | "sc_put" => (actions plan).any (· matches .write _ _ _ .put)
  | "sc_inc" => (actions plan).any (· matches .write _ _ _ .inc)
  | "sc_sum" => (actions plan).any (· matches .observe (.sum _))
  | "sc_fill" => plan.steps.any (· matches .fill ..)
  | "sc_mk" => plan.steps.any (· matches .made ..)
  | "sc_tail" => plan.steps.any (· matches .tail ..)
  | "sc_get" => (actions plan).any (· matches .observe (.get ..))
  | "sc_len" => (actions plan).any (· matches .observe (.len _))
  | _ => false

def imports (plan : Plan) : List String :=
  let type := plan.element
  ["import * from std;", "import * from std.unsigned;"] ++
    (if type.signed then ["import * from std.signed;"] else []) ++
    (if unchecked plan then [if type.signed then "import * from std.unchecked.signed;" else
      "import * from std.unchecked.unsigned;"] else []) ++
    ["import * from std.dispatch;"] ++
    (if type.signed && type.bytes < 32 then ["import { signextend as sc_signextend } from std.opcodes;"] else [])

def helperLines (plan : Plan) : List String :=
  let name := plan.element.name
  let loop := "for (let sc_i: uint256 = 0; sc_i < sc_v.length; sc_i += 1) {"
  let helpers : List (String × List String) := [
    ("sc_put", ["function sc_put(sc_c: memref<" ++ name ++ ">, sc_w: " ++ name ++ ") {",
      "    CanStore.store(sc_c, sc_w);", "}"]),
    ("sc_inc", ["function sc_inc(sc_c: memref<" ++ name ++ ">, sc_w: " ++ name ++ ") {",
      "    CanStore.store(sc_c, (CanStore.load(sc_c) + sc_w));", "}"]),
    ("sc_sum", ["function sc_sum(sc_v: " ++ name ++ "[]) returns (" ++ name ++ ") {",
      "    let sc_t: " ++ name ++ " = 0;", "    " ++ loop, "        sc_t += sc_v[sc_i];", "    }",
      "    return sc_t;", "}"]),
    ("sc_fill", ["function sc_fill(sc_v: " ++ name ++ "[], sc_w: " ++ name ++ ") {", "    " ++ loop,
      "        sc_v[sc_i] = sc_w;", "    }", "}"]),
    ("sc_mk", ["function sc_mk(sc_p: " ++ name ++ ", sc_q: " ++ name ++ ") returns (" ++ name ++ "[]) {",
      "    return [sc_p, sc_q];", "}"]),
    ("sc_tail", ["function sc_tail(sc_v: " ++ name ++ "[], sc_s: uint256) returns (arraySlice<" ++ name ++ "[]>) {",
      "    return sc_v[sc_s:];", "}"]),
    ("sc_get", ["function sc_get<c>(sc_c: c, sc_i: uint256) returns (" ++ name ++ ") where (c, uint256): " ++
      "RValueIdxAccess<" ++ name ++ "> {", "    return ridx(sc_c, sc_i);", "}"]),
    ("sc_len", ["function sc_len<c>(sc_c: c) returns (uint256) where c: Length {", "    return sc_c.length;", "}"])]
  helpers.flatMap fun (helper, lines) => if uses plan helper then lines ++ [""] else []

def parameterText (type : IntType) (param : Param) (index : Nat) : String :=
  "sc_p" ++ toString index ++ ": " ++ (if param.calldata then "calldata<" ++ type.name ++ "[]>" else type.name ++ "[]")

def signature (plan : Plan) : String :=
  "run(" ++ ",".intercalate ((plan.params.map fun _ => plan.element.name ++ "[]") ++ ["uint256"]) ++ ")"

def resultLines (plan : Plan) : List String :=
  match plan.result with
  | .word => ["return uint256(sc_r);"]
  | .array name => ["return " ++ nameText name ++ ";"]
  | .copy slice => ["return toArray(sc_s" ++ toString slice ++ ");"]

def emitWith (contract : String) (plan : Plan) : EmittedProgram :=
  let type := plan.element
  let parameters := plan.params.zipIdx.map fun (param, index) => parameterText type param index
  let result := if plan.result == .word then "uint256" else type.name ++ "[]"
  let body := ["let sc_x: word = Typedef.rep(input);"] ++
    plan.values.zipIdx.map (fun (input, index) => valueDeclaration type input index) ++
    plan.indices.zipIdx.map (fun (input, index) => indexDeclaration input index) ++
    ["let sc_r: word = 0;"] ++ stepsLines plan ++ resultLines plan
  let field := if plan.usesStorage then ["    sc_st: " ++ type.name ++ "[];", ""] else []
  let lines := imports plan ++ [""] ++ helperLines plan ++ ["contract " ++ contract ++ " {"] ++ field ++
    ["    function run(" ++ ", ".intercalate (parameters ++ ["input: uint256"]) ++ ") public returns (" ++ result ++
      ") {"] ++ indent 8 body ++ ["    }", "}"]
  { source := String.intercalate "\n" lines ++ "\n", contractName := contract, methodName := "run",
    methodSignature := signature plan, deployPath := [contract ++ "Deploy"],
    runtimePath := [contract ++ "Deploy", contract] }

def emitMemory (plan : Plan) : EmittedProgram := emitWith memoryContract plan

def emitAbi (plan : Plan) : EmittedProgram := emitWith abiContract plan

end Solcore.Synthesis.Source.Arrays
end

section
-- leanmerge: from Solcore.Synthesis.Source.ArrayCases
/-! The cases of the two array profiles, `runtime-memory-arrays` and
`runtime-array-abi`. A case retains its plan, drawn from the case seed, and
the plan's complete original Core reference at the case input, built from the
plan, never from the source. The reference's left injection is the fold, or
for `runtime-array-abi` the return data and its length; its right injection is
the revert data, a length and two Words, observed as the bytes they hold.
Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Arrays
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Core.Integers (IntType Op)

/-- What tells the two profiles apart: their names, versions and keys, the
plans they admit, how they draw, emit and shape a plan. -/
structure Profile where
  caseSchema : String
  planSchema : String
  profileVersion : String
  emitterVersion : String
  wrapperVersion : String
  planKey : String
  shapesKey : String
  originKind : String
  stage : String
  label : String
  admitted : Plan → Bool
  generate : UInt64 → Plan
  emit : Plan → EmittedProgram
  shapes : Plan → List (String × List String)
  minimumNodes : Nat

/-- The node budget, which bounds the applied reference, at least the
profile's minimum, and the decode bound of a saved reference. -/
def defaultNodes : Nat := 1024
def maximumNodes : Nat := 2048
def caseLimit : Nat := 4096

/-- An admitted plan whose reference passes the full Core checker. The input
is a literal, so the check at zero holds at every input. -/
structure CheckedPlan (profile : Profile) where private mk ::
  plan : Plan
  admitted : profile.admitted plan = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? {profile : Profile} (plan : Plan) : Option (CheckedPlan profile) :=
  if admitted : profile.admitted plan = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program {profile : Profile} (plan : CheckedPlan profile) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput (profile : Profile) where
  plan : CheckedPlan profile
  input : Word

/-! Plan JSON. Every decoder is strict and the decoded plan must re-encode to
the saved JSON. -/

private def natText (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => if toString value == text then .ok value else .error "noncanonical array plan number"
  | none => .error "array plan number is not decimal"

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

private def list (json : Json) : Except String (List Json) := do
  return (← json.getArr?).toList

def typeOf (text : String) : Except String IntType :=
  match IntType.all.find? (·.name == text) with
  | some type => .ok type
  | none => .error "unknown array element type"

def opOf (text : String) : Except String Op :=
  match Op.all.find? (·.name == text) with
  | some op => .ok op
  | none => .error "unknown array operation"

def indexJson : Index → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input index => Json.mkObj [("input", toJson index)]
  | .counter => toJson "counter"

def indexOf (json : Json) : Except String Index := do
  if json == toJson "counter" then return .counter
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  throw "unknown array index"

def valueJson : Arrays.Value → Json
  | .input index => Json.mkObj [("input", toJson index)]
  | .literal index => Json.mkObj [("literal", toJson index)]

def valueOf (json : Json) : Except String Arrays.Value := do
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  if let .ok index := json.getObjValAs? Nat "literal" then return .literal index
  throw "unknown array value"

def lengthJson : Length → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input index => Json.mkObj [("input", toJson index)]

def lengthOf (json : Json) : Except String Length := do
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  if let .ok index := json.getObjValAs? Nat "input" then return .input index
  throw "unknown array length"

def nameJson : Arrays.Name → Json
  | .var index => Json.mkObj [("var", toJson index)]
  | .param index => Json.mkObj [("param", toJson index)]

def nameOf (json : Json) : Except String Arrays.Name := do
  if let .ok index := json.getObjValAs? Nat "var" then return .var index
  if let .ok index := json.getObjValAs? Nat "param" then return .param index
  throw "unknown array name"

def collJson : Coll → Json
  | .array name => Json.mkObj [("array", nameJson name)]
  | .slice index => Json.mkObj [("slice", toJson index)]
  | .storage => toJson "storage"
  | .row grid index => Json.mkObj [("row", Json.mkObj [("grid", toJson grid), ("index", indexJson index)])]
  | .calldata index => Json.mkObj [("calldata", toJson index)]

def collOf (json : Json) : Except String Coll := do
  if json == toJson "storage" then return .storage
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok index := json.getObjValAs? Nat "slice" then return .slice index
  if let .ok row := json.getObjVal? "row" then
    return .row (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
  if let .ok index := json.getObjValAs? Nat "calldata" then return .calldata index
  throw "unknown array collection"

def targetJson : Arrays.Target → Json
  | .array name => Json.mkObj [("array", nameJson name)]
  | .storage => toJson "storage"
  | .row grid index => Json.mkObj [("row", Json.mkObj [("grid", toJson grid), ("index", indexJson index)])]

def targetOf (json : Json) : Except String Arrays.Target := do
  if json == toJson "storage" then return .storage
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok row := json.getObjVal? "row" then
    return .row (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
  throw "unknown array target"

def formJson : Form → Json
  | .plain => toJson "plain"
  | .compound op unchecked => Json.mkObj [("compound", Json.mkObj [("op", toJson op.name),
      ("unchecked", toJson unchecked)])]
  | .put => toJson "put"
  | .inc => toJson "inc"

def formOf (json : Json) : Except String Form := do
  if json == toJson "plain" then return .plain
  if json == toJson "put" then return .put
  if json == toJson "inc" then return .inc
  let compound ← json.getObjVal? "compound"
  return .compound (← opOf (← compound.getObjValAs? String "op")) (← compound.getObjValAs? Bool "unchecked")

def cutJson : Cut → Json
  | .range start stop => Json.mkObj [("range", Json.arr #[indexJson start, indexJson stop])]
  | .start start => Json.mkObj [("start", indexJson start)]
  | .stop stop => Json.mkObj [("stop", indexJson stop)]
  | .all => toJson "all"

def cutOf (json : Json) : Except String Cut := do
  if json == toJson "all" then return .all
  if let .ok bounds := json.getObjVal? "range" then
    match ← list bounds with
    | [start, stop] => return .range (← indexOf start) (← indexOf stop)
    | _ => throw "an array slice range has two bounds"
  if let .ok start := json.getObjVal? "start" then return .start (← indexOf start)
  if let .ok stop := json.getObjVal? "stop" then return .stop (← indexOf stop)
  throw "unknown array slice"

def observationJson : Observation → Json
  | .length coll => Json.mkObj [("length", collJson coll)]
  | .element coll index => Json.mkObj [("element", Json.mkObj [("coll", collJson coll), ("index", indexJson index)])]
  | .gridLength grid => Json.mkObj [("gridLength", toJson grid)]
  | .sum name => Json.mkObj [("sum", nameJson name)]
  | .get coll index => Json.mkObj [("get", Json.mkObj [("coll", collJson coll), ("index", indexJson index)])]
  | .len coll => Json.mkObj [("len", collJson coll)]

def observationOf (json : Json) : Except String Observation := do
  if let .ok coll := json.getObjVal? "length" then return .length (← collOf coll)
  if let .ok read := json.getObjVal? "element" then
    return .element (← collOf (← read.getObjVal? "coll")) (← indexOf (← read.getObjVal? "index"))
  if let .ok grid := json.getObjValAs? Nat "gridLength" then return .gridLength grid
  if let .ok name := json.getObjVal? "sum" then return .sum (← nameOf name)
  if let .ok read := json.getObjVal? "get" then
    return .get (← collOf (← read.getObjVal? "coll")) (← indexOf (← read.getObjVal? "index"))
  if let .ok coll := json.getObjVal? "len" then return .len (← collOf coll)
  throw "unknown array observation"

def actionJson : Action → Json
  | .write target index value form => Json.mkObj [("write", Json.mkObj [("target", targetJson target),
      ("index", indexJson index), ("value", valueJson value), ("form", formJson form)])]
  | .observe observation => Json.mkObj [("observe", observationJson observation)]

def actionOf (json : Json) : Except String Action := do
  if let .ok write := json.getObjVal? "write" then
    return .write (← targetOf (← write.getObjVal? "target")) (← indexOf (← write.getObjVal? "index"))
      (← valueOf (← write.getObjVal? "value")) (← formOf (← write.getObjVal? "form"))
  if let .ok observation := json.getObjVal? "observe" then return .observe (← observationOf observation)
  throw "unknown array action"

def stepJson : Step → Json
  | .alloc length => Json.mkObj [("alloc", lengthJson length)]
  | .literal values => Json.mkObj [("literal", Json.arr (values.map valueJson).toArray)]
  | .alias source => Json.mkObj [("alias", nameJson source)]
  | .copy slice => Json.mkObj [("copy", toJson slice)]
  | .made left right => Json.mkObj [("made", Json.arr #[valueJson left, valueJson right])]
  | .slice base cut => Json.mkObj [("slice", Json.mkObj [("base", collJson base), ("cut", cutJson cut)])]
  | .tail source start => Json.mkObj [("tail", Json.mkObj [("source", nameJson source), ("start", indexJson start)])]
  | .grid length => Json.mkObj [("grid", lengthJson length)]
  | .gridOf sources => Json.mkObj [("gridOf", Json.arr (sources.map nameJson).toArray)]
  | .gridLiteral rows => Json.mkObj [("gridLiteral", Json.arr (rows.map fun row =>
      Json.arr (row.map valueJson).toArray).toArray)]
  | .setRow grid index source => Json.mkObj [("setRow", Json.mkObj [("grid", toJson grid), ("index", indexJson index),
      ("source", nameJson source)])]
  | .act action => actionJson action
  | .fill target value => Json.mkObj [("fill", Json.mkObj [("target", nameJson target), ("value", valueJson value)])]
  | .push value => Json.mkObj [("push", valueJson value)]
  | .pop => toJson "pop"
  | .setLength length => Json.mkObj [("setLength", lengthJson length)]
  | .loop over body => Json.mkObj [("loop", Json.mkObj [("over", collJson over),
      ("body", Json.arr (body.map actionJson).toArray)])]

def stepOf (json : Json) : Except String Step := do
  if json == toJson "pop" then return .pop
  if let .ok length := json.getObjVal? "alloc" then return .alloc (← lengthOf length)
  if let .ok values := json.getObjVal? "literal" then return .literal (← (← list values).mapM valueOf)
  if let .ok source := json.getObjVal? "alias" then return .alias (← nameOf source)
  if let .ok slice := json.getObjValAs? Nat "copy" then return .copy slice
  if let .ok values := json.getObjVal? "made" then
    match ← list values with
    | [left, right] => return .made (← valueOf left) (← valueOf right)
    | _ => throw "an array helper takes two values"
  if let .ok slice := json.getObjVal? "slice" then
    return .slice (← collOf (← slice.getObjVal? "base")) (← cutOf (← slice.getObjVal? "cut"))
  if let .ok tail := json.getObjVal? "tail" then
    return .tail (← nameOf (← tail.getObjVal? "source")) (← indexOf (← tail.getObjVal? "start"))
  if let .ok length := json.getObjVal? "grid" then return .grid (← lengthOf length)
  if let .ok sources := json.getObjVal? "gridOf" then return .gridOf (← (← list sources).mapM nameOf)
  if let .ok rows := json.getObjVal? "gridLiteral" then
    return .gridLiteral (← (← list rows).mapM fun row => do (← list row).mapM valueOf)
  if let .ok row := json.getObjVal? "setRow" then
    return .setRow (← row.getObjValAs? Nat "grid") (← indexOf (← row.getObjVal? "index"))
      (← nameOf (← row.getObjVal? "source"))
  if let .ok fill := json.getObjVal? "fill" then
    return .fill (← nameOf (← fill.getObjVal? "target")) (← valueOf (← fill.getObjVal? "value"))
  if let .ok value := json.getObjVal? "push" then return .push (← valueOf value)
  if let .ok length := json.getObjVal? "setLength" then return .setLength (← lengthOf length)
  if let .ok loop := json.getObjVal? "loop" then
    return .loop (← collOf (← loop.getObjVal? "over")) (← (← array loop "body").mapM actionOf)
  return .act (← actionOf json)

def resultJson : Result → Json
  | .word => toJson "word"
  | .array name => Json.mkObj [("array", nameJson name)]
  | .copy slice => Json.mkObj [("copy", toJson slice)]

def resultOf (json : Json) : Except String Result := do
  if json == toJson "word" then return .word
  if let .ok name := json.getObjVal? "array" then return .array (← nameOf name)
  if let .ok slice := json.getObjValAs? Nat "copy" then return .copy slice
  throw "unknown array result"

def paramLengthJson : ParamLength → Json
  | .literal value => Json.mkObj [("literal", toJson value)]
  | .input shift mask => Json.mkObj [("shift", toJson shift), ("mask", toJson mask)]

def paramLengthOf (json : Json) : Except String ParamLength := do
  if let .ok value := json.getObjValAs? Nat "literal" then return .literal value
  return .input (← json.getObjValAs? Nat "shift") (← json.getObjValAs? Nat "mask")

def planJsonWith (schema : String) (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson schema), ("element", toJson plan.element.name),
  ("values", Json.arr (plan.values.map fun value => Json.mkObj [("offset", toJson (toString value.offset)),
    ("raw", toJson value.raw)]).toArray),
  ("indices", Json.arr (plan.indices.map fun index => Json.mkObj [("shift", toJson index.shift),
    ("mask", toJson index.mask), ("flagged", toJson index.flagged)]).toArray),
  ("params", Json.arr (plan.params.map fun param => Json.mkObj [("calldata", toJson param.calldata),
    ("length", paramLengthJson param.length), ("offset", toJson (toString param.offset)),
    ("raw", toJson param.raw)]).toArray),
  ("steps", Json.arr (plan.steps.map stepJson).toArray), ("result", resultJson plan.result)]

def planOfWith (schema : String) (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = schema do throw "unsupported array plan schema"
  let element ← typeOf (← json.getObjValAs? String "element")
  let values ← (← array json "values").mapM fun item => do
    let offset ← natText (← item.getObjValAs? String "offset")
    let raw ← item.getObjValAs? Bool "raw"
    return ({offset, raw} : ValueInput)
  let indices ← (← array json "indices").mapM fun item => do
    let shift ← item.getObjValAs? Nat "shift"
    let mask ← item.getObjValAs? Nat "mask"
    let flagged ← item.getObjValAs? Bool "flagged"
    return ({shift, mask, flagged} : IndexInput)
  let params ← (← array json "params").mapM fun item => do
    let calldata ← item.getObjValAs? Bool "calldata"
    let length ← paramLengthOf (← item.getObjVal? "length")
    let offset ← natText (← item.getObjValAs? String "offset")
    let raw ← item.getObjValAs? Bool "raw"
    return ({calldata, length, offset, raw} : Param)
  let steps ← (← array json "steps").mapM stepOf
  let result ← resultOf (← json.getObjVal? "result")
  return {element, values, indices, params, steps, result}

namespace Profile

def planJson (profile : Profile) (plan : Plan) : Json := planJsonWith profile.planSchema plan

def checkedPlan (profile : Profile) (json : Json) : Except String (CheckedPlan profile) := do
  let plan ← planOfWith profile.planSchema json
  unless profile.admitted plan do
    throw (profile.label ++ " plan is outside the admitted types, inputs, parameters, steps and operands")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed the full Core checker")
  unless json == profile.planJson plan do
    throw ("saved " ++ profile.label ++ " plan differs from its canonical checked representation")
  unless plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return checked

def shapesJson (profile : Profile) (plan : Plan) : Json :=
  Json.mkObj ((profile.shapes plan).map fun (dimension, values) => (dimension, toJson values))

end Profile

/-! Observation: the left injection is the fold or the return data, the right
injection the revert data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

/-- A returned Word, return data, or revert data. -/
inductive Observed where
  | word (value : Word)
  | output (data : List Nat)
  | reverted (data : List Nat)
  deriving BEq

private def packetWords : Solcore.Core.Value → List Nat
  | .pair (.word head) rest => head.val :: packetWords rest
  | .word last => [last.val]
  | _ => []

def Observed.ofValue? : Solcore.Core.Value → Option Observed
  | .inLeft _ (.word returned) => some (.word returned)
  | .inLeft _ packet => match packetWords packet with
      | length :: words =>
          if length ≤ 32 * words.length then some (.output ((words.flatMap wordBytes).take length)) else none
      | [] => none
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe {profile : Profile} (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.output data) => [("status", toJson "returned"), ("output", toJson (hexBytes data))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def calldata (plan : Plan) (input : Word) : String := hexBytes (plan.calldata input.val)

def contractJson (plan : Plan) (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (calldata plan input)), ("constructorCalldata", toJson "0x")]

namespace Profile

def makeCase (profile : Profile) (plan : CheckedPlan profile) (input : Word) (emitted : EmittedProgram) (origin : Json)
    (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson profile.caseSchema), (profile.planKey, profile.planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profile.profileVersion),
      ("generatorVersion", toJson arrayVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson profile.emitterVersion), ("wrapperVersion", toJson profile.wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      (profile.shapesKey, profile.shapesJson plan.plan)]),
    ("contract", contractJson plan.plan emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (profile : Profile) (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) :
    Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return profile.makeCase plan input (profile.emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (profile : Profile) (json : Json) : Except String (CheckedInput profile) := do
  unless (← json.getObjValAs? String "schema") = profile.caseSchema do
    throw ("unsupported semantic " ++ profile.label ++ " case schema")
  let plan ← profile.checkedPlan (← json.getObjVal? profile.planKey)
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw ("saved Core program differs from its " ++ profile.label ++ " plan's reference and runtime input")
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes {profile : Profile} (plan : CheckedPlan profile) (fuel : Nat) : Except String (List Observed) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some outcome => .ok outcome
        | none => .error "boundary observation did not return or revert"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- At least two outcomes differ; with the identity filter, the Words are not
the inputs. -/
def inputSensitive {profile : Profile} (plan : CheckedPlan profile) (fuel : Nat) (acceptance : Acceptance := .profile) :
    Except String Unit := do
  let outcomes ← boundaryOutcomes plan fuel
  unless outcomes.any (fun outcome => outcomes.any (fun other => outcome != other)) do
    throw "all eight boundary inputs had the same outcome"
  let words := outcomes.filterMap fun outcome => match outcome with
    | .word value => some value
    | .output data => if data.length = 32 then some (Word.ofNatModulo (data.foldl (fun acc byte => acc * 256 + byte) 0))
        else none
    | .reverted _ => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (profile : Profile) (seed : Seed) (nodes : Nat) : Except String (CheckedPlan profile) := do
  let plan := (profile.generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw (profile.label ++ " reference exceeds the node budget")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed admission or the full Core checker")
  return checked

def generatedOrigin (profile : Profile) (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson profile.originKind), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (profile : Profile) (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless profile.minimumNodes ≤ nodes && nodes ≤ maximumNodes do
          throw (profile.label ++ " node budget is outside " ++ toString profile.minimumNodes ++ " to 2,048")
        let plan ← profile.generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson profile.stage), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := profile.emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := acceptance.record (inputSelection.record (profile.generatedOrigin seed nodes inputIndex fuel))
              cases := cases.push (profile.makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

end Profile

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

def CheckedInput.measure {profile : Profile} (value : CheckedInput profile) : Measure :=
  ⟨value.plan.plan.size, value.input.val⟩

structure Reduction {profile : Profile} (source : CheckedInput profile) where private mk ::
  candidate : CheckedInput profile
  strict : candidate.measure.StrictlySmaller source.measure

private def sealReduction {profile : Profile} (source : CheckedInput profile) (plan : Plan) (input : Word) :
    Option (Reduction source) := do
  let plan ← CheckedPlan.ofPlan? (profile := profile) plan
  guard (plan.plan.nodes ≤ caseLimit)
  let candidate : CheckedInput profile := ⟨plan, input⟩
  if strict : candidate.measure.StrictlySmaller source.measure then some ⟨candidate, strict⟩ else none

/-- The plan reductions with the input kept; then the inputs 0, 1 and half the
input with the plan kept. -/
def reductions {profile : Profile} (source : CheckedInput profile) : List (Reduction source) := Id.run do
  let input := source.input
  let raw := (source.plan.plan.reductions).map (fun plan => (plan, input)) ++
    [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (input.val / 2)].map fun value => (source.plan.plan, value)
  let mut seen : List String := []
  let mut result := []
  for (plan, input) in raw do
    if let some reduced := sealReduction source plan input then
      let key := (profile.planJson reduced.candidate.plan.plan).compress ++ toString reduced.candidate.input.val
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

namespace Profile

def replayCase (profile : Profile) (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← profile.caseProgram json
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("profileVersion", profile.profileVersion), ("generatorVersion", arrayVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", profile.emitterVersion), ("wrapperVersion", profile.wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := profile.emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw ("saved source differs from emission of the " ++ profile.label ++ " plan")
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.plan emitted admitted.input do
    throw ("saved contract metadata differs from the " ++ profile.label ++ " wrapper")
  unless (← provenance.getObjVal? profile.shapesKey) == profile.shapesJson admitted.plan.plan do
    throw ("saved " ++ profile.label ++ " shapes differ from the plan")
  let kind ← origin.getObjValAs? String "kind"
  unless kind = profile.originKind || kind = "imported" || kind = "reduced" do
    throw ("unsupported " ++ profile.label ++ " case origin")
  if kind = profile.originKind then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless profile.minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← profile.generatedPlan (Seed.ofNat seed) nodes
    unless profile.planJson plan.plan == profile.planJson admitted.plan.plan do
      throw ("saved " ++ profile.label ++ " plan differs from its generation seed")
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let acceptance ← Acceptance.ofOrigin origin
    inputSensitive plan validationFuel acceptance
    unless origin == acceptance.record (inputSelection.record
        (profile.generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel)) do
      throw ("generated " ++ profile.label ++ " provenance is not canonical")
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw ("imported " ++ profile.label ++ " provenance is not canonical")
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput profile := ⟨← profile.checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw ("saved " ++ profile.label ++ " reduction is not strictly smaller than its checked parent")
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw ("reduced " ++ profile.label ++ " provenance is not canonical")
  let fresh := profile.makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw (profile.label ++ " provenance contains unexpected fields")
  return fresh

/-- A shrink response stops before its compressed cases would exceed 1.5 MB,
below the campaign's 2 MiB tool-output limit. -/
def shrinkBytes : Nat := 1500000

def shrinkCases (profile : Profile) (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← profile.replayCase json fuel
  let source ← profile.caseProgram json
  let mut cases : Array Json := #[]
  let mut bytes := 0
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", profile.planJson source.plan.plan),
      ("parentInput", toJson (toString source.input.val))]
    let case ← profile.emitCase reduced.candidate.plan reduced.candidate.input origin fuel
    let size := case.compress.utf8ByteSize
    if bytes + size > shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Profile

end Solcore.Synthesis.Source.Arrays
end

section
-- leanmerge: from Solcore.Synthesis.Source.ArrayAbiCases
/-! A `runtime-array-abi` case: an array plan of one integer element type with
one or two `T[]` or `calldata<T[]>` parameters made from the input Word,
whose steps read, write, slice and copy them and memory arrays and grids,
returning the fold or a `T[]`. Its reference panics as the memory-array
reference does, or reverts with std's `DirtyHigherBitsForInteger()` for a
narrow element std's decoder does not admit. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayAbi
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Source.Arrays (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-array-abi-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.array-abi-plan.v1",
  profileVersion := "runtime-array-abi-v1/plan-seed-v1",
  emitterVersion := Arrays.abiEmitterVersion, wrapperVersion := Arrays.abiWrapperVersion,
  planKey := "arrayAbiPlan", shapesKey := "arrayAbiShapes",
  originKind := "array-abi-generated", stage := "array-abi-profile", label := "array ABI",
  admitted := Plan.abiAdmitted, generate := generateAbi, emit := Arrays.emitAbi,
  shapes := Plan.abiShapes, minimumNodes := 512 }

def maximumNodes : Nat := Arrays.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Arrays.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.ArrayAbi
end

section
-- leanmerge: from Solcore.Synthesis.Source.MemoryArrayCases
/-! A `runtime-memory-arrays` case: an array plan of one integer element type
whose steps make, alias, copy, slice and write memory arrays, grids and the
storage array and fold what they observe, at an input that `run(uint256)`
receives. Its reference panics with `Panic(0x11)`, `Panic(0x12)`,
`Panic(0x31)`, `Panic(0x32)` or `Panic(0x41)`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryArrays
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Arrays
open Solcore.Synthesis.Source.Arrays (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-memory-array-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.memory-array-plan.v1",
  profileVersion := "runtime-memory-arrays-v1/plan-seed-v1",
  emitterVersion := Arrays.memoryEmitterVersion, wrapperVersion := Arrays.memoryWrapperVersion,
  planKey := "memoryArrayPlan", shapesKey := "memoryArrayShapes",
  originKind := "memory-array-generated", stage := "memory-array-profile", label := "memory array",
  admitted := Plan.memoryAdmitted, generate := generateMemory, emit := Arrays.emitMemory,
  shapes := Plan.memoryShapes, minimumNodes := 256 }

def maximumNodes : Nat := Arrays.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Arrays.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.MemoryArrays
end
