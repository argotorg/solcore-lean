import Solcore.Synthesis.Core.Integers

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
