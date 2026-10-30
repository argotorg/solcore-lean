import Solcore.Synthesis.Core.MemoryValues

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

def callsVersion : String := "core-memory-calls-v1"

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
  .lambda .word (.sum .word .unit) (state.builder.close (.inLeft .unit (state.ref state.acc)) state.abort)

def resultType : Ty := .sum .word .unit

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
