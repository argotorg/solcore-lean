import Solcore.Synthesis.Internal.MemoryValues

/-!
# Profile: memory calls

The profile `runtime-memory-calls`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.MemoryCalls
/-! Memory values across function and type boundaries, the plans of the
`runtime-memory-calls` profile: one to three helpers that take a
`memory<bytes>`, `memory_ref`, generic, Word-array, pair, std sum or enum
value with an index and a Word, and read it, write through it and return it,
return a slice or a fresh copy of it, pack it into a pair, take it out of a
pair, sum or enum, or call an earlier helper; and a straight-line `run` that
builds values with `runtime-memory-values`' actions, calls the helpers
directly or through function values, builds data values and closures that
capture a value, and folds every observation into `sc_r`.

The original Core reference is `runtime-memory-values`' byte-list model: a
value is its static length and its bytes packed into Words, a slice a start
and a length over its value. Every call is inlined at its call site: a
returned argument is the same value, a returned slice a view of it, a copy a
new value, and a write in a helper is seen through every variable, slice,
data value and closure that holds the value. Nothing here reads source
text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryCalls

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)
open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Width Fold Var Scope State)

def callsVersion : String := "core-memory-calls-v2"

/-- A helper's parameter: `memory<bytes>`, `memory_ref`, a type `a` bounded
by `MemorySize`, `MemoryPointer` and `MemoryEncode`, `memory<DynArray<uint256>>`,
`(memory<bytes>, word)`, `sum<memory<bytes>, word>` or the enum `Sc_E`. -/
inductive Param where
  | bytes
  | slice
  | generic
  | array
  | pair
  | sum
  | enum
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a helper or closure observes of a memory value. -/
inductive Obs where
  | length
  | word
  | byte
  | hash
  | element
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Kind where
  | read (obs : Obs) (op : Fold)
  | write (width : Width)
  | view (start : Nat)
  | copy
  | call (callee constant : Nat)
  | pack (constant : Nat)
  | take (obs : Obs) (op : Fold) (written : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `sc_h<k>(sc_v: P, sc_i: word, sc_w: word)`. -/
structure Helper where
  param : Param
  kind : Kind
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A call's argument: a memory variable or a data variable. -/
inductive Arg where
  | value (ref : Ref)
  | pair (number : Nat)
  | sum (number : Nat)
  | enum (number : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Form where
  | direct
  | value
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A data value of `run`: `(sc_b, W)`, `inl(sc_b)`, `inr(W)`,
`Sc_E.Sc_E0(sc_b, W)` or `Sc_E.Sc_E1(W)`. -/
inductive Datum where
  | pair (ref : Ref) (word : Operand)
  | inl (ref : Ref)
  | inr (word : Operand)
  | first (ref : Ref) (word : Operand)
  | second (word : Operand)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Step where
  | action (action : MemoryValues.Action)
  | call (helper : Nat) (arg : Arg) (index : Index) (word : Operand) (form : Form) (fold : Fold) (constant : Nat)
  | data (datum : Datum)
  | closure (ref : Ref) (obs : Obs)
  | apply (closure : Nat) (index : Index) (fold : Fold) (constant : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  helpers : List Helper
  steps : List Step
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Bounds. -/

def maximumHelpers : Nat := 3
def maximumSteps : Nat := 12
def maximumData : Nat := 2
def maximumClosures : Nat := 2
def maximumValues : Nat := 3
def maximumStart : Nat := 32

/-- A call's argument kind, and what a helper's result is at it. -/
inductive Kinded where
  | bytes
  | slice
  | array
  | pair
  | sum
  | enum
  | word
  deriving Repr, BEq, DecidableEq, Inhabited

def Param.accepts : Param → Kinded → Bool
  | .bytes, .bytes | .slice, .slice | .array, .array | .pair, .pair | .sum, .sum | .enum, .enum => true
  | .generic, .bytes | .generic, .slice => true
  | _, _ => false

def refKind : Ref → Kinded
  | .bytes _ => .bytes
  | .slice _ => .slice
  | .array _ => .array

def Arg.kinded : Arg → Kinded
  | .value ref => refKind ref
  | .pair _ => .pair
  | .sum _ => .sum
  | .enum _ => .enum

/-- The observations a parameter admits. -/
def Obs.admits : Param → Obs → Bool
  | .bytes, .element | .slice, .element | .generic, .element => false
  | .bytes, _ | .slice, _ | .generic, _ => true
  | .array, .element => true
  | _, _ => false

def Obs.indexed : Obs → Bool
  | .word | .byte | .element => true
  | _ => false

def Fold.admitted (constant : Nat) : Bool := MemoryValues.foldConstants.contains constant

/-- A helper is admitted on its own: its kind fits its parameter, and a call
calls an earlier helper whose parameter takes this one's. -/
def Helper.admitted (helpers : List Helper) (index : Nat) (helper : Helper) : Bool :=
  match helper.kind with
  | .read obs _ => obs.admits helper.param
  | .write width => match helper.param with
      | .bytes | .slice | .generic => true
      | .array => width == .word
      | _ => false
  | .view start => [Param.bytes, .slice, .generic].contains helper.param && start ≤ maximumStart
  | .copy => [Param.bytes, .slice, .generic].contains helper.param
  | .call callee constant =>
      callee < index && 1 ≤ constant && constant ≤ 255 &&
      match helpers[callee]? with
      | some target => target.param == helper.param ||
          (target.param == .generic && [Param.bytes, .slice, .generic].contains helper.param)
      | none => false
  | .pack constant => helper.param == .bytes && 1 ≤ constant && constant ≤ 255
  | .take obs _ _ => [Param.pair, .sum, .enum].contains helper.param && obs.admits .bytes

/-- The base kind a call reaches through `call` helpers, with the constants
added to its Word on the way. -/
def resolve (helpers : List Helper) : Nat → Nat → Option (Helper × Nat)
  | 0, _ => none
  | fuel + 1, index => do
      let helper ← helpers[index]?
      match helper.kind with
      | .call callee constant => do
          let (base, added) ← resolve helpers fuel callee
          return (base, added + constant)
      | _ => return (helper, 0)

/-- What a helper returns at an argument kind. -/
def resultAt (helpers : List Helper) (index : Nat) (arg : Kinded) : Option Kinded := do
  let (base, _) ← resolve helpers (maximumHelpers + 1) index
  match base.kind with
  | .read .. | .take .. => some .word
  | .write _ => some arg
  | .view _ => some .slice
  | .copy => some .bytes
  | .pack _ => some .pair
  | .call .. => none

/-! The scope: `runtime-memory-values`' variables and the data values and
closures of `run`. A data value or closure holds the value its variable
named when it was built. -/

inductive Held where
  | pair (var : Var)
  | inl (var : Var)
  | inr
  | first (var : Var)
  | second
  deriving Repr, BEq, DecidableEq, Inhabited

def Held.var? : Held → Option Var
  | .pair var | .inl var | .first var => some var
  | _ => none

structure Env where
  scope : Scope := {}
  pairs : List Var := []
  sums : List Held := []
  enums : List Held := []
  closures : List (Ref × Var × Obs) := []
  values : Nat := 0
  deriving Repr, BEq, Inhabited

private def need (condition : Bool) : Option Unit := if condition then some () else none

namespace Env

def held? (env : Env) : Arg → Option Held
  | .value _ => none
  | .pair number => env.pairs[number]?.map Held.pair
  | .sum number => env.sums[number]?
  | .enum number => env.enums[number]?

/-- The memory value a call reaches through its argument, if any. -/
def target? (env : Env) (arg : Arg) : Option Var :=
  match arg with
  | .value ref => env.scope.var? ref
  | _ => (env.held? arg).bind Held.var?

def declare (env : Env) (kind : Kinded) (var : Var) : Option Env :=
  let scope := env.scope
  match kind with
  | .bytes => if scope.bytes.length < MemoryValues.maximumBytes then
      some {env with scope := {scope with bytes := scope.bytes ++ [some var]}} else none
  | .slice => if scope.slices.length < MemoryValues.maximumSlices then
      some {env with scope := {scope with slices := scope.slices ++ [some var]}} else none
  | .array => if scope.arrays.length < MemoryValues.maximumArrays then
      some {env with scope := {scope with arrays := scope.arrays ++ [some var]}} else none
  | .pair => if env.pairs.length < maximumData then some {env with pairs := env.pairs ++ [var]} else none
  | _ => none

/-- The in-range positions of an observation of `var`. -/
def obsValid? (var : Var) : Obs → Option Nat
  | .length | .hash => some 1
  | .word => MemoryValues.Width.valid? .word var.length
  | .byte => MemoryValues.Width.valid? .byte var.length
  | .element => some var.length

/-- Check a call's index against what the helper's base kind does with the
value it reaches: an unused index is the literal 0. -/
def callIndex (base : Helper) (var? : Option Var) (index : Index) : Bool :=
  let unused := index == .literal 0
  match base.kind, var? with
  | .read obs _, some var | .take obs _ false, some var =>
      if obs.indexed then (obsValid? var obs).any fun valid => index.admitted false valid else unused
  | .take obs _ true, some var =>
      -- the byte write and, when indexed, the observation share the index
      (MemoryValues.Width.valid? .byte var.length).any (fun valid => index.admitted false valid) &&
        (!obs.indexed || (obsValid? var obs).any fun valid => index.admitted false valid)
  | .write width, some var =>
      ((if base.param == .array then some var.length else MemoryValues.Width.valid? width var.length).any
        fun valid => index.admitted false valid)
  | _, _ => unused

/-- The static effect of a call on the scope, or `none`. -/
def call? (env : Env) (helpers : List Helper) (helper : Nat) (arg : Arg) (index : Index) (word : Operand)
    (fold : Fold) (constant : Nat) : Option (Env × Kinded) := do
  let callee ← helpers[helper]?
  need (callee.param.accepts arg.kinded && word.admitted false)
  let (base, _) ← resolve helpers (maximumHelpers + 1) helper
  let result ← resultAt helpers helper arg.kinded
  let held := env.held? arg
  let var? := env.target? arg
  match arg with
  | .value _ => need var?.isSome
  | _ => need held.isSome
  need (callIndex base var? index)
  if result == .word then need (Fold.admitted constant) else need (fold == .add && constant = 3)
  match base.kind with
  | .view start =>
      let var ← var?
      need (start ≤ var.length)
      let env ← env.declare .slice {var with start := var.start + start, length := var.length - start}
      return (env, result)
  | .copy =>
      let var ← var?
      need (var.length + 32 ≤ MemoryValues.maximumLength)
      let object := env.scope.objects.length
      let env := {env with scope := {env.scope with objects := env.scope.objects ++ [(false, var.length + 32)]}}
      let env ← env.declare .bytes {object, start := 0, length := var.length + 32}
      return (env, result)
  | .write _ =>
      let var ← var?
      let env ← env.declare result var
      return (env, result)
  | .pack _ =>
      let var ← var?
      let env ← env.declare .pair var
      return (env, result)
  | _ => return (env, result)

def datum? (env : Env) : Datum → Option Env
  | .pair ref word => do
      need (refKind ref == .bytes && word.admitted false)
      env.declare .pair (← env.scope.var? ref)
  | .inl ref => do
      need (refKind ref == .bytes && env.sums.length < maximumData)
      return {env with sums := env.sums ++ [.inl (← env.scope.var? ref)]}
  | .inr word => do
      need (word.admitted false && env.sums.length < maximumData)
      return {env with sums := env.sums ++ [.inr]}
  | .first ref word => do
      need (refKind ref == .bytes && word.admitted false && env.enums.length < maximumData)
      return {env with enums := env.enums ++ [.first (← env.scope.var? ref)]}
  | .second word => do
      need (word.admitted false && env.enums.length < maximumData)
      return {env with enums := env.enums ++ [.second]}

def step? (env : Env) (helpers : List Helper) : Step → Option Env
  | .action action => do
      need (match action with
        | .write _ _ value _ _ => value.admitted false
        | _ => true)
      return {env with scope := ← env.scope.step? false action}
  | .call helper arg index word form fold constant => do
      let (env, _) ← env.call? helpers helper arg index word fold constant
      need (form == .direct || env.values < maximumValues)
      return {env with values := env.values + (if form == .value then 1 else 0)}
  | .data datum => env.datum? datum
  | .closure ref obs => do
      let var ← env.scope.var? ref
      need ((if ref.isArray then obs == .element else obs != .element) && env.closures.length < maximumClosures)
      need ((obsValid? var obs).isSome)
      return {env with closures := env.closures ++ [(ref, var, obs)]}
  | .apply closure index _ constant => do
      let (_, var, obs) ← env.closures[closure]?
      need (Fold.admitted constant)
      if obs.indexed then
        let valid ← obsValid? var obs
        need (index.admitted false valid)
      else need (index == .literal 0)
      return env

end Env

/-- The hashes a step runs: a hashing observation, call or closure. -/
def Step.hashes (helpers : List Helper) (env : Env) : Step → Bool
  | .action single => single.hashes
  | .call target arg .. => match resolve helpers (maximumHelpers + 1) target with
      | some ({kind := .read .hash _, ..}, _) => true
      | some ({kind := .take .hash _ _, ..}, _) => ((env.held? arg).bind Held.var?).isSome
      | _ => false
  | .apply number .. => match env.closures[number]? with
      | some (_, _, .hash) => true
      | _ => false
  | _ => false

def Step.observes (helpers : List Helper) (env : Env) : Step → Bool
  | .action single => single.observes
  | .call target arg .. => let _ := env; resultAt helpers target arg.kinded == some .word
  | .apply .. => true
  | _ => false

namespace Plan

/-- The scope after every step, with the hashes and observations so far. -/
def scan? (plan : Plan) : Option (Env × Nat × Bool) :=
  plan.steps.foldlM (init := (({} : Env), 0, false)) fun (env, hashes, observed) step => do
    let next ← env.step? plan.helpers step
    return (next, hashes + (if step.hashes plan.helpers env then 1 else 0), observed || step.observes plan.helpers env)

/-- At least one call, and an observation. -/
def admitted (plan : Plan) : Bool :=
  1 ≤ plan.helpers.length && plan.helpers.length ≤ maximumHelpers &&
  plan.helpers.zipIdx.all (fun (helper, index) => helper.admitted plan.helpers index) &&
  1 ≤ plan.steps.length && plan.steps.length ≤ maximumSteps &&
  plan.steps.any (fun step => match step with
    | .call .. => true
    | _ => false) &&
  match plan.scan? with
  | some (_, hashes, observed) => observed && hashes ≤ MemoryValues.maximumHashes
  | none => false

def hashes (plan : Plan) : Bool :=
  match plan.scan? with
  | some (_, count, _) => count > 0
  | none => false

end Plan

/-! The reference compiler: `runtime-memory-values`' state, the data values
and closures of `run` as the values they hold, and every call inlined. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)

structure Compiler where
  state : State
  env : Env := {}
  /-- The bound Word of every pair, sum and enum value that carries one. -/
  words : List (List (Option Nat)) := [[], [], []]

namespace Compiler

def obsAccess (obs : Obs) (index : Index) : MemoryValues.Access :=
  match obs with
  | .length => .length
  | .word => .word index
  | .byte => .byte index
  | .hash => .hash
  | .element => .element index false

def combine (fold : Fold) (left right : Expr) : Expr :=
  match fold with
  | .add => .binary .wordAdd left right
  | .xor => .binary .wordXor left right

/-- The Word a data value carries, by kind (0 pairs, 1 sums, 2 enums). -/
def carried (compiler : Compiler) (kind number : Nat) : Option Nat :=
  ((compiler.words[kind]?).bind (·[number]?)).join

def addCarried (compiler : Compiler) (kind : Nat) (position : Option Nat) : Compiler :=
  {compiler with words := compiler.words.set kind (compiler.words.getD kind [] ++ [position])}

/-- Inline one call: its base kind with the Word bound once; a Word result
is returned for folding, a value result declared. -/
def call (compiler : Compiler) (helpers : List Helper) (helper : Nat) (arg : Arg) (index : Index)
    (word : Operand) : Compiler × Option Expr := Id.run do
  let some (base, added) := resolve helpers (maximumHelpers + 1) helper | return (compiler, none)
  let some result := resultAt helpers helper arg.kinded | return (compiler, none)
  let state := compiler.state
  let (state, wordPosition) := state.bind
    (if added = 0 then state.operand word else .binary .wordAdd (state.operand word) (num added))
  let compiler := {compiler with state}
  let target := compiler.env.target? arg
  match base.kind, target with
  | .read obs fold, some var =>
      let (state, observed) := compiler.state.access var (obsAccess obs index)
      return ({compiler with state}, some (combine fold observed (state.ref wordPosition)))
  | .write width, some var =>
      let ref : Ref := if arg.kinded == .array then .array 0 else .bytes 0
      let state := compiler.state.write ref var index (compiler.state.ref wordPosition) width
      let env := (compiler.env.declare result var).getD compiler.env
      return ({compiler with state, env}, none)
  | .view start, some var =>
      let env := (compiler.env.declare .slice {var with start := var.start + start, length := var.length - start}).getD compiler.env
      return ({compiler with env}, none)
  | .copy, some var =>
      let state := compiler.state
      let (state, positions) := state.bindAll (MemoryValues.State.view var)
      let words := MemoryValues.State.concatenation [(positions, var.length), ([wordPosition], 32)]
      let (state, bound) := state.bindAll words
      let object := compiler.env.scope.objects.length
      let state := state.setValue object bound
      let env := {compiler.env with scope := {compiler.env.scope with objects := compiler.env.scope.objects ++ [(false, var.length + 32)]}}
      let env := (env.declare .bytes {object, start := 0, length := var.length + 32}).getD env
      return ({compiler with state, env}, none)
  | .pack constant, some var =>
      let state := compiler.state
      let (state, carried) := state.bind (.binary .wordAdd (state.ref wordPosition) (num constant))
      let env := (compiler.env.declare .pair var).getD compiler.env
      return ((({compiler with state, env} : Compiler).addCarried 0 (some carried)), none)
  | .take obs fold written, some var =>
      let carriedWord := match arg with
        | .pair number => compiler.carried 0 number
        | .enum number => compiler.carried 2 number
        | _ => some wordPosition
      let state := if written then
          compiler.state.write (.bytes 0) var index (compiler.state.ref (carriedWord.getD wordPosition)) .byte
        else compiler.state
      let (state, observed) := state.access var (obsAccess obs index)
      return ({compiler with state}, some (combine fold observed (state.ref wordPosition)))
  | .take _ fold _, none =>
      let carriedWord := match arg with
        | .sum number => compiler.carried 1 number
        | .enum number => compiler.carried 2 number
        | _ => none
      let state := compiler.state
      return (compiler, some (combine fold (state.ref (carriedWord.getD wordPosition)) (state.ref wordPosition)))
  | _, _ => return (compiler, none)

def fold (compiler : Compiler) (fold : Fold) (constant : Nat) (observed : Expr) : Compiler :=
  let state := compiler.state
  let scaled := Expr.binary .wordMul (state.ref state.acc) (num constant)
  let (state, acc) := state.bind (combine fold scaled observed)
  {compiler with state := {state with acc}}

/-- One step; the state's scope follows the environment's after it. -/
def step (compiler : Compiler) (helpers : List Helper) (step : Step) : Compiler :=
  let env := (compiler.env.step? helpers step).getD compiler.env
  let compiler := {compiler with state := {compiler.state with scope := compiler.env.scope}}
  let compiler : Compiler := match step with
  | .action action =>
      let state := compiler.state.action false action
      {compiler with state, env := {compiler.env with scope := state.scope}}
  | .call helper arg index word _ fold constant =>
      let (compiler, observed) := compiler.call helpers helper arg index word
      let compiler := {compiler with env := {compiler.env with values := env.values}}
      match observed with
      | some value => compiler.fold fold constant value
      | none => compiler
  | .data datum =>
      let compiler := {compiler with env}
      let state := compiler.state
      match datum with
      | .pair _ word =>
          let (state, position) := state.bind (state.operand word)
          ({compiler with state} : Compiler).addCarried 0 (some position)
      | .inl _ => compiler.addCarried 1 none
      | .inr word =>
          let (state, position) := state.bind (state.operand word)
          ({compiler with state} : Compiler).addCarried 1 (some position)
      | .first _ word =>
          let (state, position) := state.bind (state.operand word)
          ({compiler with state} : Compiler).addCarried 2 (some position)
      | .second word =>
          let (state, position) := state.bind (state.operand word)
          ({compiler with state} : Compiler).addCarried 2 (some position)
  | .closure .. => {compiler with env}
  | .apply closure index fold constant =>
      match compiler.env.closures[closure]? with
      | some (_, var, obs) =>
          let (state, observed) := compiler.state.access var (obsAccess obs index)
          ({compiler with state} : Compiler).fold fold constant observed
      | none => compiler
  {compiler with state := {compiler.state with scope := compiler.env.scope}}

end Compiler

namespace Plan

/-- `fun input => …`: the hash closure when the plan hashes, the
accumulator's zero, every step with its calls inlined, then the left
injection of the accumulator. -/
def expression (plan : Plan) : Expr :=
  let state : State := {builder := {size := 1}, input := 0}
  let state := if plan.hashes then
      let (state, closure) := state.bind MemoryValues.hashClosure
      {state with hash := some closure}
    else state
  let (state, acc) := state.bind (num 0)
  let compiler := plan.steps.foldl (fun compiler step => compiler.step plan.helpers step)
    ({state := {state with acc}} : Compiler)
  let state := compiler.state
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
def budgetNodes (plan : Plan) : Nat := plan.nodes - (if plan.hashes then MemoryValues.hashNodes else 0)

end Plan

/-! Specified shapes, from the plan. -/

def Param.name : Param → String
  | .bytes => "bytes"
  | .slice => "slice"
  | .generic => "generic"
  | .array => "array"
  | .pair => "pair"
  | .sum => "sum"
  | .enum => "enum"

def Obs.name : Obs → String
  | .length => "length"
  | .word => "word"
  | .byte => "byte"
  | .hash => "hash"
  | .element => "element"

def Kind.name : Kind → String
  | .read .. => "read"
  | .write _ => "write"
  | .view _ => "view"
  | .copy => "copy"
  | .call .. => "call"
  | .pack _ => "pack"
  | .take .. => "take"

def Kinded.name : Kinded → String
  | .bytes => "bytes"
  | .slice => "slice"
  | .array => "array"
  | .pair => "pair"
  | .sum => "sum"
  | .enum => "enum"
  | .word => "word"

def Datum.name : Datum → String
  | .pair .. => "pair"
  | .inl _ => "inl"
  | .inr _ => "inr"
  | .first .. => "enum0"
  | .second _ => "enum1"

def indexKind : Index → String
  | .literal _ => "literal"
  | .input .. => "input"
  | .counter .. => "counter"

/-- The writes and observations of every value, in plan order, for the
hazards: a write through one variable, slice, data value or helper seen
through another, a copy unaffected by a later write to its source, and a
closure that sees a write made after it. -/
structure Trace where
  shapes : List (String × String) := []
  /-- `(value, through, helper)` of every write so far. -/
  writes : List (Nat × String × Bool) := []
  /-- `(copy, source, writes to the source before it)`. -/
  copies : List (Nat × Nat × Nat) := []
  /-- `(value, writes to it before the closure)` of every closure. -/
  captures : List (Nat × Nat) := []

def Trace.add (trace : Trace) (dimension value : String) : Trace :=
  {trace with shapes := trace.shapes ++ [(dimension, value)]}

def Trace.writesTo (trace : Trace) (object : Nat) : Nat := (trace.writes.filter (·.1 == object)).length

def refName : Ref → String
  | .bytes number => "sc_b" ++ toString number
  | .slice number => "sc_s" ++ toString number
  | .array number => "sc_a" ++ toString number

def Arg.name : Arg → String
  | .value ref => refName ref
  | .pair number => "sc_t" ++ toString number
  | .sum number => "sc_u" ++ toString number
  | .enum number => "sc_e" ++ toString number

/-- An observation of `object` through `through`. -/
def Trace.observe (trace : Trace) (object : Nat) (through : String) : Trace :=
  let trace := trace.writes.foldl (fun trace (written, writer, helper) =>
    if written != object then trace
    else
      let trace := if writer != through then trace.add "hazards" "alias" else trace
      if helper then trace.add "hazards" "helper" else trace) trace
  if trace.copies.any (fun (copy, source, before) => copy == object && trace.writesTo source > before)
  then trace.add "hazards" "copy" else trace

/-- The variable a call's value result is declared as, in the scope after it. -/
def Env.declared (env : Env) : Kinded → Option Arg
  | .bytes => some (.value (.bytes (env.scope.bytes.length - 1)))
  | .slice => some (.value (.slice (env.scope.slices.length - 1)))
  | .array => some (.value (.array (env.scope.arrays.length - 1)))
  | .pair => some (.pair (env.pairs.length - 1))
  | _ => none

/-- The helpers a call runs, from the one it names to its base kind. -/
def chain (helpers : List Helper) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, index => match helpers[index]? with
      | some {kind := .call callee _, ..} => index :: chain helpers fuel callee
      | some _ => [index]
      | none => []

/-- An input index that can leave the `valid` in-range positions. -/
def wide (index : Index) (valid : Option Nat) : Bool :=
  match index, valid with
  | .input _ modulus, some valid => modulus > valid
  | _, _ => false

def Plan.shapes (plan : Plan) : List (String × List String) := Id.run do
  let mut trace : Trace := {}
  let mut env : Env := {}
  -- `(generic helper, argument kind)` of every instance
  let mut instances : List (Nat × String) := []
  -- the variables value results were declared as
  let mut returned : List Arg := []
  for helper in plan.helpers do
    trace := trace.add "helpers" (helper.kind.name ++ ":" ++ helper.param.name)
  for step in plan.steps do
    match step with
    | .action single =>
        trace := trace.add "steps" ("action:" ++ single.kind)
        match single with
        | .write target .. =>
            if let some var := env.scope.var? target then
              trace := {trace with writes := trace.writes ++ [(var.object, refName target, false)]}
        | .observe _ _ value _ =>
            if let some var := env.scope.var? value then trace := trace.observe var.object (refName value)
        | .bytes (.toBytes (.value source)) | .bytes (.concat (.value source) _) | .bytes (.concat _ (.value source)) =>
            if let some var := env.scope.var? source then
              trace := {trace with copies := trace.copies ++ [(env.scope.objects.length, var.object, trace.writesTo var.object)]}
        | _ => pure ()
    | .call helper arg index _ form _ _ =>
        let result := (resultAt plan.helpers helper arg.kinded).getD .word
        trace := (trace.add "calls" (match form with
          | .direct => "direct:" ++ result.name
          | .value => "value:" ++ result.name)).add "steps" "call"
        if returned.contains arg then trace := trace.add "passes" arg.kinded.name
        for number in chain plan.helpers (maximumHelpers + 1) helper do
          if (plan.helpers[number]?).any (·.param == .generic) then
            trace := trace.add "instances" arg.kinded.name
            instances := instances ++ [(number, arg.kinded.name)]
        if let some (base, _) := resolve plan.helpers (maximumHelpers + 1) helper then
          let var? := env.target? arg
          match base.kind, var? with
          | .read obs _, some var =>
              if obs.indexed then trace := trace.add "indices" (obs.name ++ ":" ++ indexKind index)
              if wide index (Env.obsValid? var obs) then trace := trace.add "ranges" "call"
              trace := trace.add "observations" (obs.name ++ ":" ++ arg.kinded.name)
              trace := trace.observe var.object arg.name
          | .write width, some var =>
              let access := if base.param == .array then "set" else if width == .word then "put" else "put8"
              trace := trace.add "indices" (access ++ ":" ++ indexKind index)
              let valid := if base.param == .array then some var.length else MemoryValues.Width.valid? width var.length
              if wide index valid then trace := trace.add "ranges" "call"
              trace := {trace with writes := trace.writes ++ [(var.object, arg.name, true)]}
          | .copy, some var =>
              trace := {trace with copies := trace.copies ++ [(env.scope.objects.length, var.object, trace.writesTo var.object)]}
          | .take obs _ written, some var =>
              if written then
                trace := trace.add "indices" ("put8:" ++ indexKind index)
                if wide index (MemoryValues.Width.valid? .byte var.length) then trace := trace.add "ranges" "call"
                trace := {trace with writes := trace.writes ++ [(var.object, arg.name, true)]}
              if obs.indexed then trace := trace.add "indices" (obs.name ++ ":" ++ indexKind index)
              if obs.indexed && wide index (Env.obsValid? var obs) then trace := trace.add "ranges" "call"
              trace := trace.add "observations" (obs.name ++ ":" ++ arg.kinded.name)
              trace := trace.observe var.object arg.name
          | .take .., none => trace := trace.add "observations" ("carried:" ++ arg.kinded.name)
          | _, _ => pure ()
    | .data datum =>
        trace := (trace.add "data" datum.name).add "steps" "data"
    | .closure ref obs =>
        trace := (trace.add "closures" (obs.name ++ ":" ++ (refKind ref).name)).add "steps" "closure"
        if let some var := env.scope.var? ref then
          trace := {trace with captures := trace.captures ++ [(var.object, trace.writesTo var.object)]}
    | .apply number index _ _ =>
        trace := trace.add "steps" "apply"
        if let some (ref, var, obs) := env.closures[number]? then
          if obs.indexed then trace := trace.add "indices" (obs.name ++ ":" ++ indexKind index)
          if wide index (Env.obsValid? var obs) then trace := trace.add "ranges" "apply"
          if (trace.captures[number]?).any (fun (object, before) => trace.writesTo object > before) then
            trace := trace.add "hazards" "closure"
          trace := trace.observe var.object (refName ref)
    env := (env.step? plan.helpers step).getD env
    if let .call helper arg .. := step then
      if let some declared := env.declared ((resultAt plan.helpers helper arg.kinded).getD .word) then
        returned := returned ++ [declared]
  -- one generic helper at both argument kinds
  if instances.any (fun (number, kind) => instances.any fun (other, otherKind) => other == number && otherKind != kind) then
    trace := trace.add "instances" "several"
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let of := fun (dimension : String) => sorted (trace.shapes.filterMap fun (name, value) =>
    if name == dimension then some value else none)
  return [("helpers", of "helpers"), ("calls", of "calls"), ("passes", of "passes"), ("instances", of "instances"),
    ("data", of "data"),
    ("closures", of "closures"), ("observations", of "observations"), ("indices", of "indices"),
    ("ranges", of "ranges"), ("hazards", of "hazards"), ("steps", of "steps")]

/-! Generation. -/

def domain : UInt64 := 0x6d656d63616c0001

private def pick {α : Type} [Inhabited α] (values : List α) : Gen α := do
  return values[← draw values.length]!

def drawFold : Gen Fold := do return if (← draw 2) = 0 then .add else .xor

def drawObs (param : Param) : Gen Obs := do
  if param == .array then return .element
  match ← drawWeighted [1, 3, 2, 2] with
  | 0 => return .length
  | 1 => return .word
  | 2 => return .byte
  | _ => return .hash

/-- The parameter that takes what a helper returns, if it returns a value. -/
def Helper.returns (helpers : List Helper) (index : Nat) (helper : Helper) : Option Param :=
  match resolve helpers (maximumHelpers + 1) index with
  | some ({kind := .write _, ..}, _) => some helper.param
  | some ({kind := .view _, ..}, _) => some .slice
  | some ({kind := .copy, ..}, _) => some .bytes
  | some ({kind := .pack _, ..}, _) => some .pair
  | _ => none

/-- A helper's parameter is an earlier helper's a third of the time, so that
it may call that helper, and takes what an earlier helper returns another
third of the time. -/
def drawHelper (helpers : List Helper) : Gen Helper := do
  let index := helpers.length
  let returned := helpers.zipIdx.filterMap fun (helper, number) => helper.returns helpers number
  let choice ← if index > 0 then draw 6 else pure 5
  let param ← if choice < 2 then pure (← pick helpers).param
    else if choice < 4 && !returned.isEmpty then pick returned
    else match ← drawWeighted [3, 2, 3, 1, 1, 1, 1] with
    | 0 => pure Param.bytes
    | 1 => pure .slice
    | 2 => pure .generic
    | 3 => pure .array
    | 4 => pure .pair
    | 5 => pure .sum
    | _ => pure .enum
  let callees := (List.range index).filter fun callee => match helpers[callee]? with
    | some target => target.param == param || (target.param == .generic && [Param.bytes, .slice, .generic].contains param)
    | none => false
  let memory := [Param.bytes, .slice, .generic].contains param
  let data := [Param.pair, .sum, .enum].contains param
  let weights := [
    if data then 0 else 3,
    if data then 0 else 3,
    if memory then 2 else 0,
    if memory then 2 else 0,
    if callees.isEmpty then 0 else 3,
    if param == .bytes then 2 else 0,
    if data then 4 else 0]
  let kind ← match ← drawWeighted weights with
    | 0 => pure (Kind.read (← drawObs param) (← drawFold))
    | 1 => pure (Kind.write (if param == .array || (← draw 2) = 0 then .word else .byte))
    | 2 => pure (Kind.view (← draw (maximumStart + 1)))
    | 3 => pure Kind.copy
    | 4 => pure (Kind.call (← pick callees) (1 + (← draw 255)))
    | 5 => pure (Kind.pack (1 + (← draw 255)))
    | _ => pure (Kind.take (← drawObs .bytes) (← drawFold) ((← draw 2) = 0))
  return {param, kind}

/-- A call's index for what its base kind does with the value it reaches. -/
def drawCallIndex (base : Helper) (var? : Option Var) : Gen Index := do
  let positions : Option Nat := match base.kind, var? with
    | .read obs _, some var | .take obs _ false, some var => if obs.indexed then Env.obsValid? var obs else none
    | .take obs _ true, some var =>
        let byte := MemoryValues.Width.valid? .byte var.length
        if obs.indexed then (byte.bind fun b => (Env.obsValid? var obs).map (min b)) else byte
    | .write width, some var => if base.param == .array then some var.length else MemoryValues.Width.valid? width var.length
    | _, _ => none
  match positions with
  | none => return .literal 0
  | some valid =>
      if (← draw 2) = 0 then return .literal (← draw valid)
      return .input (← pick MemoryValues.shifts) (1 + (← draw (valid + MemoryValues.indexSlack)))

/-- The arguments in scope a helper takes. -/
def Env.arguments (env : Env) (param : Param) : List Arg :=
  let values := env.scope.visible.filterMap fun ref =>
    if param.accepts (refKind ref) && (env.scope.var? ref).isSome then some (Arg.value ref) else none
  values ++ (List.range env.pairs.length).filterMap (fun n => if param.accepts .pair then some (Arg.pair n) else none) ++
    (List.range env.sums.length).filterMap (fun n => if param.accepts .sum then some (Arg.sum n) else none) ++
    (List.range env.enums.length).filterMap (fun n => if param.accepts .enum then some (Arg.enum n) else none)

def drawWord : Gen Operand := MemoryValues.drawOperand false

/-- Whether a helper's base kind can take a value of `length` bytes: an
indexed access needs an in-range position, a view its start and a copy room
for its Word. -/
def Helper.reaches (base : Helper) (length : Nat) : Bool :=
  let positions := fun (obs : Obs) => match obs with
    | .word => 32 ≤ length
    | .byte => 1 ≤ length
    | _ => true
  match base.kind with
  | .read obs _ => positions obs
  | .take obs _ written => positions obs && (!written || 1 ≤ length)
  | .write width => base.param == .array || (if width == .word then 32 ≤ length else 1 ≤ length)
  | .view start => start ≤ length
  | .copy => length + 32 ≤ MemoryValues.maximumLength
  | _ => true

def Env.fits (env : Env) (base : Helper) (arg : Arg) : Bool :=
  (env.target? arg).all fun var => base.reaches var.length

/-- A step that makes an argument of `param` available, if one is needed: a
bytes value built as `runtime-memory-values` builds one, a cut of a value in
scope, a Word array, or a data value of a bytes value in scope. -/
def provide (env : Env) (base : Helper) (param : Param) : Gen (Option Step) := do
  if (env.arguments param).any (env.fits base) then return none
  let fitting := fun (ref : Ref) => (env.scope.var? ref).any fun var => base.reaches var.length
  let build : Gen (Option Step) := do
    let built ← MemoryValues.drawBuild env.scope false
    if (MemoryValues.Scope.buildLength? env.scope false built).any base.reaches then
      return some (.action (.bytes built))
    return some (.action (.bytes (.concat (.word (← drawWord)) (.word (← drawWord)))))
  match param with
  | .bytes | .generic => build
  | .slice =>
      match env.scope.sources.filter fitting with
      | [] => build
      | sources =>
          let ref ← pick sources
          let length := ((env.scope.var? ref).map (·.length)).getD 0
          let cut ← MemoryValues.drawCut length
          if ((MemoryValues.Cut.apply? length cut).map (·.2)).any base.reaches then return some (.action (.slice ref cut))
          return some (.action (.slice ref (.drop 0)))
  | .array =>
      let count := 1 + (← draw MemoryValues.maximumElements)
      let mut elements : List Operand := []
      for _ in List.range count do elements := elements ++ [← drawWord]
      return some (.action (.array false elements))
  | .pair | .sum | .enum =>
      match env.scope.visible.filter (fun ref => refKind ref == .bytes && fitting ref) with
      | [] => build
      | bytes =>
          let ref ← pick bytes
          let memory := (← draw 3) != 0
          let word ← drawWord
          match param with
          | .pair => return some (.data (.pair ref word))
          | .sum => return some (.data (if memory then .inl ref else .inr word))
          | _ => return some (.data (if memory then .first ref word else .second word))

/-- A follow-up: an observation of a value, a write, a closure or its
application, a second variable, or a bytes value built from what is in
scope. -/
def drawExtra (env : Env) (hash : Bool) : Gen (Option Step) := do
  let visible := env.scope.visible
  if visible.isEmpty then return none
  match ← drawWeighted [5, 2, 1, if env.closures.isEmpty then 0 else 3, 1, 2] with
  | 0 => return some (.action (← MemoryValues.drawObserve env.scope false hash))
  | 1 =>
      if env.scope.targets.isEmpty then return none
      return some (.action (← MemoryValues.drawWrite env.scope false))
  | 2 =>
      if env.closures.length ≥ maximumClosures then return none
      let ref ← pick visible
      let obs ← if refKind ref == .array then pure Obs.element else drawObs .bytes
      return some (.closure ref (if obs == .hash && !hash then .length else obs))
  | 3 =>
      let number ← draw env.closures.length
      let (_, var, obs) := env.closures.getD number default
      let mut index : Index := .literal 0
      if obs.indexed then
        if let some valid := Env.obsValid? var obs then
          if (← draw 2) = 0 then index := .literal (← draw valid)
          else index := .input (← pick MemoryValues.shifts) (1 + (← draw (valid + MemoryValues.indexSlack)))
      return some (.apply number index (← drawFold) (← pick MemoryValues.foldConstants))
  | 4 =>
      let bytes := visible.filter fun ref => refKind ref == .bytes
      if bytes.isEmpty then return none
      return some (.action (.alias (← pick bytes)))
  | _ => return some (.action (.bytes (← MemoryValues.drawBuild env.scope false)))

/-- One to three helpers, then for each helper in order one or two calls,
each after the steps that make its argument and up to one other step, and
followed by up to one more; a call takes a value an earlier call returned
half the time when one fits. A plan without an observation ends with one. -/
def drawPlan : Gen Plan := do
  let count := 1 + (← draw maximumHelpers)
  let mut helpers : List Helper := []
  for _ in List.range count do helpers := helpers ++ [← drawHelper helpers]
  let mut env : Env := {}
  let mut steps : List Step := []
  let mut hashes := 0
  let mut returned : List Arg := []
  let place := fun (env : Env) (steps : List Step) (step : Step) => do
    if steps.length < maximumSteps then
      if let some next := env.step? helpers step then return some (next, step)
    return none
  for index in List.range count do
    let helper := helpers.getD index default
    let some (base, _) := resolve helpers (maximumHelpers + 1) index | continue
    for _ in List.range (1 + (← draw 2)) do
      for _ in List.range 2 do
        if let some step ← provide env base helper.param then
          if let some (next, step) ← place env steps step then
            env := next
            steps := steps ++ [step]
      if (← draw 2) = 0 then
        if let some step ← drawExtra env (hashes < MemoryValues.maximumHashes) then
          if let some (next, step) ← place env steps step then
            if step.hashes helpers env then hashes := hashes + 1
            env := next
            steps := steps ++ [step]
      let arguments := (env.arguments helper.param).filter (env.fits base)
      if arguments.isEmpty then continue
      let passed := arguments.filter returned.contains
      let arg ← if !passed.isEmpty && (← draw 2) = 0 then pick passed else pick arguments
      let indexValue ← drawCallIndex base (env.target? arg)
      let word ← drawWord
      let form := if (← draw 3) = 0 then Form.value else .direct
      let result := (resultAt helpers index arg.kinded).getD .word
      let (fold, constant) ← if result == .word then do pure (← drawFold, ← pick MemoryValues.foldConstants)
        else pure (Fold.add, 3)
      let step := Step.call index arg indexValue word form fold constant
      let hashing := step.hashes helpers env
      if hashing && hashes ≥ MemoryValues.maximumHashes then continue
      if let some (next, step) ← place env steps step then
        if hashing then hashes := hashes + 1
        env := next
        steps := steps ++ [step]
        if let some declared := next.declared result then returned := returned ++ [declared]
      if (← draw 2) = 0 then
        if let some step ← drawExtra env (hashes < MemoryValues.maximumHashes) then
          if let some (next, step) ← place env steps step then
            if step.hashes helpers env then hashes := hashes + 1
            env := next
            steps := steps ++ [step]
  let plan : Plan := {helpers, steps}
  if plan.admitted then return plan
  -- no observation yet: observe the first bytes value or array
  match env.scope.visible.head? with
  | some ref =>
      let observe := Step.action (.observe .add 3 ref (if refKind ref == .array then .element (.literal 0) false else .length))
      let candidate : Plan := {helpers, steps := steps.take (maximumSteps - 1) ++ [observe]}
      return candidate
  | none => return plan

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- Steps are dropped from the end while the budgeted reference exceeds
`nodes`, more than one step remains and the rest is still admitted. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.steps.length do
    let shorter : Plan := {plan with steps := plan.steps.dropLast}
    if plan.budgetNodes > nodes && plan.steps.length > 1 && shorter.admitted then
      plan := shorter
  return plan

end Solcore.Synthesis.Core.MemoryCalls
end

section
-- leanmerge: from Solcore.Synthesis.Core.MemoryCallsShrink
/-! Reductions of memory call plans. A candidate is kept only when the plan
is admitted and strictly smaller: in its structure first, then in the sum of
its numeric literals. A call weighs more than the actions it amounts to, so
inlining one is a reduction. Removing a declaration or a helper renumbers what
comes after it; a candidate that would still refer to it is not formed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MemoryCalls

open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Fold Width)

private def plus (left right : Nat × Nat) : Nat × Nat := (left.1 + right.1, left.2 + right.2)

private def observed (obs : Obs) (fold : Fold) : Nat :=
  (if obs == .length then 1 else 2) + (if fold == .xor then 1 else 0)

def Kind.size : Kind → Nat × Nat
  | .read obs fold => (observed obs fold, 0)
  | .write width => (if width == .byte then 2 else 1, 0)
  | .view start => (1, start)
  | .copy => (1, 0)
  | .call callee constant => (2, callee + constant)
  | .pack constant => (1, constant)
  | .take obs fold written => (observed obs fold + (if written then 1 else 0), 0)

def Param.size : Param → Nat
  | .generic => 2
  | _ => 1

def Helper.size (helper : Helper) : Nat × Nat := plus (1 + helper.param.size, 0) helper.kind.size

def Datum.size : Datum → Nat × Nat
  | .pair _ word | .first _ word => plus (4, 0) word.size
  | .inl _ => (4, 0)
  | .inr word | .second word => plus (2, 0) word.size

def Step.size : Step → Nat × Nat
  | .action single => plus (1, 0) single.size
  | .call helper _ index word form fold constant =>
      plus (6 + (if form == .value then 1 else 0) + (if fold == .xor then 1 else 0), helper + constant)
        (plus index.size word.size)
  | .data datum => datum.size
  | .closure _ obs => (if obs == .length then 2 else 3, 0)
  | .apply number index fold constant => plus (2 + (if fold == .xor then 1 else 0), number + constant) index.size

/-- Structure first, then literals; literals stay far below `2 ^ 16`. -/
def Plan.size (plan : Plan) : Nat :=
  let total := (plan.helpers.map Helper.size ++ plan.steps.map Step.size).foldl plus (0, 0)
  total.1 * 2 ^ 16 + total.2

/-! Renumbering and substitution. -/

/-- What a step declares, by kind: `bytes`, `slice`, `array`, `pair`, `sum`,
`enum` or `closure`. A function value is named by its position alone. -/
def Step.declares (helpers : List Helper) : Step → Option String
  | .action single => single.declares {}
  | .call helper arg .. => match resultAt helpers helper arg.kinded with
      | some .bytes => some "bytes"
      | some .slice => some "slice"
      | some .array => some "array"
      | some .pair => some "pair"
      | _ => none
  | .data (.pair ..) => some "pair"
  | .data (.inl _) | .data (.inr _) => some "sum"
  | .data (.first ..) | .data (.second _) => some "enum"
  | .closure .. => some "closure"
  | .apply .. => none

private def renumberNumber (removed number : Nat) : Option Nat :=
  if number < removed then some number else if number == removed then none else some (number - 1)

def Arg.renumber (kind : String) (removed : Nat) : Arg → Option Arg
  | .value ref => (ref.renumber kind removed 1).map .value
  | .pair number => if kind == "pair" then (renumberNumber removed number).map .pair else some (.pair number)
  | .sum number => if kind == "sum" then (renumberNumber removed number).map .sum else some (.sum number)
  | .enum number => if kind == "enum" then (renumberNumber removed number).map .enum else some (.enum number)

def Step.renumber (kind : String) (removed : Nat) : Step → Option Step
  | .action single => (single.renumber kind removed 1).map .action
  | .call helper arg index word form fold constant => do
      return .call helper (← arg.renumber kind removed) index word form fold constant
  | .data (.pair ref word) => do return .data (.pair (← ref.renumber kind removed 1) word)
  | .data (.inl ref) => do return .data (.inl (← ref.renumber kind removed 1))
  | .data (.first ref word) => do return .data (.first (← ref.renumber kind removed 1) word)
  | .data datum => some (.data datum)
  | .closure ref obs => do return .closure (← ref.renumber kind removed 1) obs
  | .apply number index fold constant =>
      if kind == "closure" then do return .apply (← renumberNumber removed number) index fold constant
      else some (.apply number index fold constant)

private def mapPart (f : Ref → Ref) : MemoryValues.Part → MemoryValues.Part
  | .value ref => .value (f ref)
  | part => part

private def mapAction (f : Ref → Ref) : MemoryValues.Action → MemoryValues.Action
  | .bytes (.toBytes part) => .bytes (.toBytes (mapPart f part))
  | .bytes (.concat left right) => .bytes (.concat (mapPart f left) (mapPart f right))
  | .slice source cut => .slice (f source) cut
  | .alias source => .alias (f source)
  | .write target index value width form => .write (f target) index value width form
  | .observe fold constant value access => .observe fold constant (f value) access
  | action => action

/-- Every memory variable a step names, mapped. -/
def Step.mapRefs (f : Ref → Ref) : Step → Step
  | .action single => .action (mapAction f single)
  | .call helper (.value ref) index word form fold constant => .call helper (.value (f ref)) index word form fold constant
  | .data (.pair ref word) => .data (.pair (f ref) word)
  | .data (.inl ref) => .data (.inl (f ref))
  | .data (.first ref word) => .data (.first (f ref) word)
  | .closure ref obs => .closure (f ref) obs
  | step => step

/-- The number a step's declaration gets: its kind's declarations before it. -/
def Plan.declaredBefore (plan : Plan) (index : Nat) (kind : String) : Nat :=
  ((plan.steps.take index).filter fun step => step.declares plan.helpers == some kind).length

/-! Plan reductions. -/

/-- Drop a step, a call among them. -/
def Plan.removeStep (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let rest := plan.steps.drop (index + 1)
  let rest ← match step.declares plan.helpers with
    | some kind => rest.mapM (·.renumber kind (plan.declaredBefore index kind))
    | none => some rest
  return {plan with steps := plan.steps.take index ++ rest}

/-- Replace the value a writing call returns by its argument: the write stays
as the action it amounts to, and every later use of the result names the
argument. -/
def Plan.passThrough (plan : Plan) (index : Nat) : Option Plan := do
  let step ← plan.steps[index]?
  let .call helper (.value ref) indexValue word .. := step | none
  let (base, _) ← resolve plan.helpers (maximumHelpers + 1) helper
  let .write width := base.kind | none
  let kind ← step.declares plan.helpers
  let result := plan.declaredBefore index kind
  let substitute := fun (target : Ref) => if target.kind == kind && target.number == result then ref else target
  let rest ← (plan.steps.drop (index + 1)).mapM fun later => (later.mapRefs substitute).renumber kind result
  return {plan with steps := plan.steps.take index ++ [.action (.write ref indexValue word width .inline)] ++ rest}

/-- A call written as the `runtime-memory-values` actions its base kind
amounts to, when its argument is a memory variable; a value result keeps its
declaration. -/
def Plan.inlineCall (plan : Plan) (index : Nat) : Option Plan := do
  let .call helper (.value ref) indexValue word _ fold constant ← plan.steps[index]? | none
  let (base, _) ← resolve plan.helpers (maximumHelpers + 1) helper
  let replacement : List Step ← match base.kind with
    | .read obs _ => some [.action (.observe fold constant ref (Compiler.obsAccess obs indexValue))]
    | .view start => some [.action (.slice ref (.drop start))]
    | .copy => some [.action (.bytes (.concat (.value ref) (.word word)))]
    | .write width =>
        let declare : MemoryValues.Action := if ref.isSlice then .slice ref (.drop 0) else .alias ref
        some [.action (.write ref indexValue word width .inline), .action declare]
    | .pack _ => some [.data (.pair ref word)]
    | _ => none
  return {plan with steps := plan.steps.take index ++ replacement ++ plan.steps.drop (index + 1)}

/-- Call a `call` helper's callee directly. -/
def Plan.bypass (plan : Plan) (index : Nat) : Option Plan := do
  let .call helper arg indexValue word form fold constant ← plan.steps[index]? | none
  let target ← plan.helpers[helper]?
  let .call callee _ := target.kind | none
  return {plan with steps := plan.steps.set index (.call callee arg indexValue word form fold constant)}

/-- Remove a helper no step and no other helper calls, renumbering the rest. -/
def Plan.removeHelper (plan : Plan) (index : Nat) : Option Plan := do
  let called := plan.steps.any fun step => match step with
    | .call helper .. => helper == index
    | _ => false
  let chained := plan.helpers.any fun helper => match helper.kind with
    | .call callee _ => callee == index
    | _ => false
  if called || chained || index ≥ plan.helpers.length then none
  let shift := fun (number : Nat) => if number > index then number - 1 else number
  let helpers := (plan.helpers.eraseIdx index).map fun helper => match helper.kind with
    | .call callee constant => {helper with kind := .call (shift callee) constant}
    | _ => helper
  let steps := plan.steps.map fun step => match step with
    | .call helper arg indexValue word form fold constant => .call (shift helper) arg indexValue word form fold constant
    | other => other
  return {helpers, steps}

/-! Local reductions of helpers and steps. -/

def Kind.reductions : Kind → List Kind
  | .read obs fold =>
      (if fold == .xor then [.read obs .add] else []) ++
        (if obs != .length && obs != .element then [.read .length fold] else [])
  | .write .byte => [.write .word]
  | .write .word => []
  | .view start => if start = 0 then [] else [.view 0]
  | .copy => []
  | .call callee constant => if constant > 1 then [.call callee 1] else []
  | .pack constant => if constant > 1 then [.pack 1] else []
  | .take obs fold written =>
      (if written then [.take obs fold false] else []) ++ (if fold == .xor then [.take obs .add written] else []) ++
        (if obs != .length then [.take .length fold written] else [])

def Helper.reductions (helper : Helper) : List Helper :=
  (if helper.param == .generic then [{helper with param := .bytes}, {helper with param := .slice}] else []) ++
    helper.kind.reductions.map fun kind => {helper with kind}

def Step.reductions : Step → List Step
  | .action single => single.reductions.map .action
  | .call helper arg index word form fold constant =>
      (if form == .value then [.call helper arg index word .direct fold constant] else []) ++
      (if fold == .xor then [.call helper arg index word form .add constant] else []) ++
      (if constant > 3 then [.call helper arg index word form fold 3] else []) ++
      index.reductions.map (fun reduced => .call helper arg reduced word form fold constant) ++
      word.reductions.map (fun reduced => .call helper arg index reduced form fold constant)
  | .data (.pair ref word) => word.reductions.map fun reduced => .data (.pair ref reduced)
  | .data (.inl _) => [.data (.inr .input)]
  | .data (.inr word) => word.reductions.map fun reduced => .data (.inr reduced)
  | .data (.first ref word) => .data (.second word) :: word.reductions.map fun reduced => .data (.first ref reduced)
  | .data (.second word) => word.reductions.map fun reduced => .data (.second reduced)
  | .closure ref obs => if obs == .length || obs == .element then [] else [.closure ref .length]
  | .apply number index fold constant =>
      (if fold == .xor then [.apply number index .add constant] else []) ++
      (if constant > 3 then [.apply number index fold 3] else []) ++
      index.reductions.map fun reduced => .apply number reduced fold constant

def planReductions (plan : Plan) : List Plan := Id.run do
  let mut result : List Plan := []
  for index in List.range plan.steps.length do
    for candidate in [plan.removeStep index, plan.passThrough index, plan.inlineCall index, plan.bypass index] do
      if let some reduced := candidate then result := result ++ [reduced]
  for index in List.range plan.helpers.length do
    if let some reduced := plan.removeHelper index then result := result ++ [reduced]
  for (helper, index) in plan.helpers.zipIdx do
    result := result ++ helper.reductions.map fun reduced => {plan with helpers := plan.helpers.set index reduced}
  for (step, index) in plan.steps.zipIdx do
    result := result ++ step.reductions.map fun reduced => {plan with steps := plan.steps.set index reduced}
  return result.filter fun candidate => candidate.admitted && candidate.size < plan.size

end Solcore.Synthesis.Core.MemoryCalls
end

section
-- leanmerge: from Solcore.Synthesis.Source.MemoryCallsEmitter
/-! The Solcore source of a memory call plan: the helpers `sc_h<k>(sc_v, sc_i,
sc_w)` over std's memory values and data values carrying them, the enum
`Sc_E` when a plan uses it, and `SynthesizedMemoryCalls.run(uint256)`, whose
`runtime-memory-values` actions keep that profile's text. The source is a
function of the plan; nothing here builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryCalls

open Solcore.Synthesis.Core.MemoryCalls
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def emitterVersion : String := "solcore-source-memory-calls-v1"
def wrapperVersion : String := "solcore-word-memory-calls-contract-v1"
def contractName : String := "SynthesizedMemoryCalls"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedMemoryCallsDeploy"]
def runtimePath : List String := ["SynthesizedMemoryCallsDeploy", "SynthesizedMemoryCalls"]

def kindType : Kinded → String
  | .bytes => "memory<bytes>"
  | .slice => "memory_ref"
  | .array => "memory<DynArray<uint256>>"
  | .pair => "(memory<bytes>, word)"
  | .sum => "sum<memory<bytes>, word>"
  | .enum => "Sc_E"
  | .word => "word"

def paramType : Param → String
  | .bytes => "memory<bytes>"
  | .slice => "memory_ref"
  | .generic => "a"
  | .array => "memory<DynArray<uint256>>"
  | .pair => "(memory<bytes>, word)"
  | .sum => "sum<memory<bytes>, word>"
  | .enum => "Sc_E"

private def foldText : Fold → String
  | .add => " + "
  | .xor => " ^ "

/-- What a helper's base kind returns, given the text of the value it is
handed. -/
def baseResult (base : Helper) (value : String) : String :=
  match base.kind with
  | .read .. | .take .. => "word"
  | .write _ => value
  | .view _ => "memory_ref"
  | .copy => "memory<bytes>"
  | .pack _ => "(memory<bytes>, word)"
  | .call .. => value

def obsText (value index : String) : Obs → String
  | .length => "MemorySize.len(" ++ value ++ ")"
  | .word => "sc_word(" ++ value ++ ", " ++ index ++ ")"
  | .byte => "sc_byte(" ++ value ++ ", " ++ index ++ ")"
  | .hash => "Typedef.rep(keccak256_(" ++ value ++ "))"
  | .element => "Typedef.rep(" ++ value ++ "[uint256(" ++ index ++ ")])"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def helperName (index : Nat) : String := "sc_h" ++ toString index

def helperLines (helpers : List Helper) (index : Nat) (helper : Helper) : List String :=
  let value := paramType helper.param
  let result := match resolve helpers (maximumHelpers + 1) index with
    | some (base, _) => baseResult base value
    | none => "word"
  let name := helperName index
  let header := if helper.param == .generic then
      "function " ++ name ++ "<a>(sc_v: a, sc_i: word, sc_w: word) returns (" ++ result ++
        ") where a: MemorySize, a: MemoryPointer, a: MemoryEncode {"
    else "function " ++ name ++ "(sc_v: " ++ value ++ ", sc_i: word, sc_w: word) returns (" ++ result ++ ") {"
  let body := match helper.kind with
    | .read obs fold => ["return (" ++ obsText "sc_v" "sc_i" obs ++ foldText fold ++ "sc_w);"]
    | .write width =>
        (if helper.param == .array then ["IndexAccess.set(sc_v, uint256(sc_i), uint256(sc_w));"]
         else [(if width == .word then "sc_put" else "sc_put8") ++ "(sc_v, sc_i, sc_w);"]) ++ ["return sc_v;"]
    | .view start => ["return slice_(sc_v, " ++ toString start ++ ");"]
    | .copy => ["return concat(sc_v, bytes32(sc_w));"]
    | .call callee constant => ["return " ++ helperName callee ++ "(sc_v, sc_i, (sc_w + " ++ toString constant ++ "));"]
    | .pack constant => ["return (sc_v, (sc_w + " ++ toString constant ++ "));"]
    | .take obs fold written =>
        let memory := fun (writtenWord : String) =>
          (if written then ["sc_put8(sc_p, sc_i, " ++ writtenWord ++ ");"] else []) ++
            ["return (" ++ obsText "sc_p" "sc_i" obs ++ foldText fold ++ "sc_w);"]
        let wordArm := ["return (sc_q" ++ foldText fold ++ "sc_w);"]
        let arm := fun (pattern : String) (lines : List String) =>
          ["case " ++ pattern ++ " {"] ++ indent 4 lines ++ ["}"]
        let arms := match helper.param with
          | .pair => arm "(sc_p, sc_q)" (memory "sc_q")
          | .sum => arm "inl(sc_p)" (memory "sc_w") ++ arm "inr(sc_q)" wordArm
          | _ => arm "Sc_E.Sc_E0(sc_p, sc_q)" (memory "sc_q") ++ arm "Sc_E.Sc_E1(sc_q)" wordArm
        ["match (sc_v) {"] ++ indent 4 arms ++ ["}"]
  [header] ++ indent 4 body ++ ["}", ""]

/-- Declaration numbers so far: `runtime-memory-values`' kinds, then pairs,
sums, enums, closures and function values. -/
structure Names where
  memory : MemoryValues.Names := {}
  pairs : Nat := 0
  sums : Nat := 0
  enums : Nat := 0
  closures : Nat := 0
  values : Nat := 0

def declaration (names : Names) : Kinded → String × Names
  | .bytes => ("let sc_b" ++ toString names.memory.bytes ++ ": memory<bytes>",
      {names with memory := {names.memory with bytes := names.memory.bytes + 1}})
  | .slice => ("let sc_s" ++ toString names.memory.slices ++ ": memory_ref",
      {names with memory := {names.memory with slices := names.memory.slices + 1}})
  | .array => ("let sc_a" ++ toString names.memory.arrays ++ ": memory<DynArray<uint256>>",
      {names with memory := {names.memory with arrays := names.memory.arrays + 1}})
  | .pair => ("let sc_t" ++ toString names.pairs ++ ": (memory<bytes>, word)", {names with pairs := names.pairs + 1})
  | .sum => ("let sc_u" ++ toString names.sums ++ ": sum<memory<bytes>, word>", {names with sums := names.sums + 1})
  | .enum => ("let sc_e" ++ toString names.enums ++ ": Sc_E", {names with enums := names.enums + 1})
  | .word => ("", names)

def stepLines (helpers : List Helper) (names : Names) : Step → List String × Names
  | .action single =>
      let (lines, memory) := MemoryValues.actionLines "sc_counter" names.memory single
      (lines, {names with memory})
  | .call helper arg index word form fold constant =>
      let result := (resultAt helpers helper arg.kinded).getD .word
      let arguments := arg.name ++ ", " ++ MemoryValues.indexText "sc_counter" index ++ ", " ++
        MemoryValues.operandText "sc_counter" word
      let (lines, callee, names) := match form with
        | .direct => ([], helperName helper, names)
        | .value =>
            let name := "sc_f" ++ toString names.values
            (["let " ++ name ++ ": function (" ++ kindType arg.kinded ++ ", word, word) returns (" ++
              kindType result ++ ") = " ++ helperName helper ++ ";"], name, {names with values := names.values + 1})
      let call := callee ++ "(" ++ arguments ++ ")"
      if result == .word then
        (lines ++ ["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ call ++ ");"], names)
      else
        let (declared, names) := declaration names result
        (lines ++ [declared ++ " = " ++ call ++ ";"], names)
  | .data datum =>
      let word := fun (operand : Operand) => MemoryValues.operandText "sc_counter" operand
      match datum with
      | .pair ref operand =>
          let (declared, names) := declaration names .pair
          ([declared ++ " = (" ++ refName ref ++ ", " ++ word operand ++ ");"], names)
      | .inl ref =>
          let (declared, names) := declaration names .sum
          ([declared ++ " = inl(" ++ refName ref ++ ");"], names)
      | .inr operand =>
          let (declared, names) := declaration names .sum
          ([declared ++ " = inr(" ++ word operand ++ ");"], names)
      | .first ref operand =>
          let (declared, names) := declaration names .enum
          ([declared ++ " = Sc_E.Sc_E0(" ++ refName ref ++ ", " ++ word operand ++ ");"], names)
      | .second operand =>
          let (declared, names) := declaration names .enum
          ([declared ++ " = Sc_E.Sc_E1(" ++ word operand ++ ");"], names)
  | .closure ref obs =>
      let name := "sc_c" ++ toString names.closures
      (["let " ++ name ++ ": function (word) returns (word) = lam (sc_j: word) -> word {",
        "    return " ++ obsText (refName ref) "sc_j" obs ++ ";", "};"], {names with closures := names.closures + 1})
  | .apply number index fold constant =>
      (["sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ "sc_c" ++ toString number ++ "(" ++
        MemoryValues.indexText "sc_counter" index ++ "));"], names)

/-- The memory helpers a plan uses: `runtime-memory-values`' through its
actions, and through the helpers' and closures' observations and writes. -/
def usedHelpers (plan : Plan) : List String :=
  let fromObs := fun (obs : Obs) => match obs with
    | .word => ["sc_word"]
    | .byte => ["sc_byte"]
    | _ => []
  let used := plan.steps.flatMap (fun step => match step with
      | .action single => MemoryValues.actionHelpers single
      | .closure _ obs => fromObs obs
      | _ => []) ++
    plan.helpers.flatMap fun helper => match helper.kind with
      | .read obs _ => fromObs obs
      | .write width => if helper.param == .array then [] else if width == .word then ["sc_put"] else ["sc_put8"]
      | .take obs _ written => fromObs obs ++ (if written then ["sc_put8"] else [])
      | _ => []
  MemoryValues.helperNames.filter used.contains

def usesEnum (plan : Plan) : Bool :=
  plan.helpers.any (·.param == .enum) || plan.steps.any fun step => match step with
    | .data (.first ..) | .data (.second _) => true
    | _ => false

def emit (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    let (more, next) := stepLines plan.helpers names step
    lines := lines ++ more
    names := next
  let enumLines := if usesEnum plan then
      ["enum Sc_E {", "    Sc_E0(memory<bytes>, word),", "    Sc_E1(word)", "}", ""] else []
  let source := ["import * from std;", "import * from std.dispatch;",
      "import { mload, mstore, mstore8, shr, mod } from std.opcodes;", ""] ++
    (usedHelpers plan).flatMap MemoryValues.helperLines ++ enumLines ++
    (plan.helpers.zipIdx.flatMap fun (helper, index) => helperLines plan.helpers index helper) ++
    ["contract " ++ contractName ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.MemoryCalls
end

section
-- leanmerge: from Solcore.Synthesis.Source.MemoryCallsCases
/-! A memory call case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference is
`runtime-memory-values`' byte-list model with every call inlined, built from
the plan, never from the source. Its right injection is an out-of-range
access's failure code, observed as std's revert data: `OutOfBounds()` for a
value's Words and bytes and `Panic(0x32)` for an array element. Saved
observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MemoryCalls
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.MemoryCalls
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def caseSchema : String := "solcore-lean.semantic-memory-call-case.v1"
def planSchema : String := "solcore-lean.memory-call-plan.v1"
def profileVersion : String := "runtime-memory-calls-v1/plan-seed-v1"
def outOfBounds : String := MemoryValues.outOfBounds
def arrayOutOfBounds : String := MemoryValues.arrayOutOfBounds

/-- The node budget, which bounds the applied reference without the hash
closure, and the decode bound of a saved reference. -/
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

/-! Plan JSON, with `runtime-memory-values`' encoding of operands, indices,
variables and actions. Every decoder is strict and the decoded plan must
re-encode to the saved JSON. -/

private def foldName : Fold → String
  | .add => "add"
  | .xor => "xor"

private def foldOf (text : String) : Except String Fold :=
  match text with
  | "add" => .ok .add
  | "xor" => .ok .xor
  | _ => .error "unknown memory call fold"

def paramOf (text : String) : Except String Param :=
  match text with
  | "bytes" => .ok .bytes
  | "slice" => .ok .slice
  | "generic" => .ok .generic
  | "array" => .ok .array
  | "pair" => .ok .pair
  | "sum" => .ok .sum
  | "enum" => .ok .enum
  | _ => .error "unknown memory call parameter"

def obsOf (text : String) : Except String Obs :=
  match text with
  | "length" => .ok .length
  | "word" => .ok .word
  | "byte" => .ok .byte
  | "hash" => .ok .hash
  | "element" => .ok .element
  | _ => .error "unknown memory call observation"

def helperJson (helper : Helper) : Json :=
  let fields : List (String × Json) := match helper.kind with
    | .read obs fold => [("kind", toJson "read"), ("obs", toJson obs.name), ("fold", toJson (foldName fold))]
    | .write width => [("kind", toJson "write"), ("width", toJson width.name)]
    | .view start => [("kind", toJson "view"), ("start", toJson start)]
    | .copy => [("kind", toJson "copy")]
    | .call callee constant => [("kind", toJson "call"), ("callee", toJson callee), ("constant", toJson constant)]
    | .pack constant => [("kind", toJson "pack"), ("constant", toJson constant)]
    | .take obs fold written => [("kind", toJson "take"), ("obs", toJson obs.name), ("fold", toJson (foldName fold)),
        ("written", toJson written)]
  Json.mkObj ([("param", toJson helper.param.name)] ++ fields)

def argJson (arg : Arg) : Json := toJson arg.name

def datumJson : Datum → Json
  | .pair ref word => Json.mkObj [("datum", toJson "pair"), ("value", MemoryValues.refJson ref),
      ("word", MemoryValues.operandJson word)]
  | .inl ref => Json.mkObj [("datum", toJson "inl"), ("value", MemoryValues.refJson ref)]
  | .inr word => Json.mkObj [("datum", toJson "inr"), ("word", MemoryValues.operandJson word)]
  | .first ref word => Json.mkObj [("datum", toJson "enum0"), ("value", MemoryValues.refJson ref),
      ("word", MemoryValues.operandJson word)]
  | .second word => Json.mkObj [("datum", toJson "enum1"), ("word", MemoryValues.operandJson word)]

def stepJson : Step → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .call helper arg index word form fold constant => Json.mkObj [("call", Json.mkObj [
      ("helper", toJson helper), ("arg", argJson arg), ("index", MemoryValues.indexJson index),
      ("word", MemoryValues.operandJson word),
      ("form", toJson (match form with
        | .direct => "direct"
        | .value => "value")), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .data datum => Json.mkObj [("data", datumJson datum)]
  | .closure ref obs => Json.mkObj [("closure", Json.mkObj [("value", MemoryValues.refJson ref), ("obs", toJson obs.name)])]
  | .apply number index fold constant => Json.mkObj [("apply", Json.mkObj [("closure", toJson number),
      ("index", MemoryValues.indexJson index), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]

def planJson (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("helpers", .arr (plan.helpers.map helperJson).toArray),
  ("steps", .arr (plan.steps.map stepJson).toArray)]

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def helperOf (json : Json) : Except String Helper := do
  let param ← paramOf (← json.getObjValAs? String "param")
  let kind ← match ← json.getObjValAs? String "kind" with
    | "read" => pure (Kind.read (← obsOf (← json.getObjValAs? String "obs")) (← foldOf (← json.getObjValAs? String "fold")))
    | "write" =>
        match ← json.getObjValAs? String "width" with
        | "word" => pure (Kind.write .word)
        | "byte" => pure (Kind.write .byte)
        | _ => throw "unknown memory call write width"
    | "view" => pure (Kind.view (← json.getObjValAs? Nat "start"))
    | "copy" => pure Kind.copy
    | "call" => pure (Kind.call (← json.getObjValAs? Nat "callee") (← json.getObjValAs? Nat "constant"))
    | "pack" => pure (Kind.pack (← json.getObjValAs? Nat "constant"))
    | "take" => pure (Kind.take (← obsOf (← json.getObjValAs? String "obs")) (← foldOf (← json.getObjValAs? String "fold"))
        (← json.getObjValAs? Bool "written"))
    | _ => throw "unknown memory call helper kind"
  return {param, kind}

def argOf (json : Json) : Except String Arg := do
  let text ← json.getStr?
  let number := fun (head : String) => do
    let digits := (text.drop head.length).toString
    let some value := digits.toNat? | throw "unknown memory call argument"
    unless toString value = digits do throw "noncanonical memory call argument"
    return value
  if text.startsWith "sc_t" then return .pair (← number "sc_t")
  else if text.startsWith "sc_u" then return .sum (← number "sc_u")
  else if text.startsWith "sc_e" then return .enum (← number "sc_e")
  else return .value (← MemoryValues.refOf json)

def datumOf (json : Json) : Except String Datum := do
  match ← json.getObjValAs? String "datum" with
  | "pair" => return .pair (← MemoryValues.refOf (← json.getObjVal? "value")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "inl" => return .inl (← MemoryValues.refOf (← json.getObjVal? "value"))
  | "inr" => return .inr (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum0" => return .first (← MemoryValues.refOf (← json.getObjVal? "value")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum1" => return .second (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | _ => throw "unknown memory call datum"

def stepOf (json : Json) : Except String Step := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  if let .ok call := json.getObjVal? "call" then
    let form ← match ← call.getObjValAs? String "form" with
      | "direct" => pure Form.direct
      | "value" => pure Form.value
      | _ => throw "unknown memory call form"
    return .call (← call.getObjValAs? Nat "helper") (← argOf (← call.getObjVal? "arg"))
      (← MemoryValues.indexOf (← call.getObjVal? "index")) (← MemoryValues.operandOf (← call.getObjVal? "word")) form
      (← foldOf (← call.getObjValAs? String "fold")) (← call.getObjValAs? Nat "constant")
  if let .ok datum := json.getObjVal? "data" then return .data (← datumOf datum)
  if let .ok closure := json.getObjVal? "closure" then
    return .closure (← MemoryValues.refOf (← closure.getObjVal? "value")) (← obsOf (← closure.getObjValAs? String "obs"))
  let applied ← json.getObjVal? "apply"
  return .apply (← applied.getObjValAs? Nat "closure") (← MemoryValues.indexOf (← applied.getObjVal? "index"))
    (← foldOf (← applied.getObjValAs? String "fold")) (← applied.getObjValAs? Nat "constant")

def planOf (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported memory call plan schema"
  return {helpers := ← (← array json "helpers").mapM helperOf, steps := ← (← array json "steps").mapM stepOf}

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "memory call plan is outside the admitted helpers, steps, values, lengths and indices"
  let some checked := CheckedPlan.ofPlan? plan | throw "memory call reference failed the full Core checker"
  unless json == planJson plan do throw "saved memory call plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "memory call reference exceeds the 5,120-node case limit"
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
        match MemoryValues.failureOutput? code with
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
    ("schema", toJson caseSchema), ("memoryCallPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson callsVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("memoryCallShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "memory call reference exceeds the 5,120-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic memory call case schema"
  let plan ← checkedPlan (← json.getObjVal? "memoryCallPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its memory call plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done (.inLeft _ (.word value)) _ => .ok (.word value)
    | .done (.inRight _ (.word code)) _ =>
        if (MemoryValues.failureOutput? code).isSome then .ok .outOfRange
        else .error "boundary observation failed with an unknown code"
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
  unless plan.budgetNodes ≤ nodes do throw "memory call reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "memory call reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "memory-call-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
          throw "memory call node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "memory-call-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", callsVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the memory call plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the memory call wrapper"
  unless (← provenance.getObjVal? "memoryCallShapes") == shapesJson admitted.plan.plan do
    throw "saved memory call shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "memory-call-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported memory call case origin"
  if kind = "memory-call-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved memory call plan differs from its generation seed"
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
      throw "generated memory call provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported memory call provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved memory call reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced memory call provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "memory call provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.MemoryCalls
end
