import Solcore.Synthesis.Core.MemoryValues

/-! std's `Error` values and revert paths in pure functions, the plans of the
`runtime-revert-data` profile: `Error(W)` with a selector Word computed from
the input, `Error.Empty`, `Error.Msg(s)` over a `memory<string>` view of a
bytes value built from the input, `require(C, E)`, `require(C, "literal")`
through std's `Str<Error>`, `revertLit("literal")` and `revertEmpty()`, at
sites in `run`, in helpers, closures, match arms and a bounded `while` loop,
with `Error` values made and chosen by helpers and carried by pairs, std sums
and a user enum, and `runtime-memory-values`' bytes values, writes and
observations around them.

The original Core reference is `runtime-memory-values`' byte-list model. It
returns the left injection of the accumulator, or the right injection of the
revert data: its length and its bytes in two Words. A site binds a sum that
continues or carries its payload, and every enclosing scope forwards a payload
it receives, so the first site whose condition holds decides. A message is the
bytes of its value at the site, so a write made after the `Error` was made is
seen. Every helper and closure is inlined where it runs. Nothing here reads
source text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.RevertData

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)
open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Width Fold Part Build Action Var Scope State)

def revertVersion : String := "core-revert-data-v1"

/-- A test of a Word: `(W < c)`, `(W > c)`, `(W == c)`, `(W != c)` or
`((W & m) == k)`. -/
inductive Test where
  | lt (constant : Nat)
  | gt (constant : Nat)
  | eq (constant : Nat)
  | ne (constant : Nat)
  | bits (mask value : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A condition on a Word of its scope; in a helper or closure `input` is its
own Word parameter. -/
structure Cond where
  word : Operand
  test : Test
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An `Error` made in place: `Error(W)`, `Error.Empty`, or
`Error.Msg(memory(Typedef.rep(sc_b<n>)))`. -/
inductive Make where
  | selector (word : Operand)
  | empty
  | message (value : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Where an `Error` comes from: made in place, an `Error` variable
`sc_e<n>`, or the scope's own `sc_e`, a helper's parameter or a match arm's
binding. -/
inductive Source where
  | make (make : Make)
  | named (number : Nat)
  | param
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a site reverts with: an `Error`, a literal, or nothing. -/
inductive Payload where
  | error (source : Source)
  | literal (text : Nat)
  | none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `if (C) { … }` reverts when its condition holds, `require(C, …)` when
it does not. -/
inductive Form where
  | when
  | require
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A revert site: `if (C) { revertWithError(E); }`, `require(C, E);`,
`if (C) { revertLit("…"); }`, `require(C, "…");` or
`if (C) { revertEmpty(); }`. -/
structure Site where
  form : Form
  cond : Cond
  payload : Payload
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A helper `sc_h<k>`:
- `raise`: `(sc_e: Error, sc_w: word) returns (word)`, its site over `sc_w`,
  then `return (sc_w op c);`;
- `make`: `(sc_w: word) returns (Error)`, `return Error((sc_w + c));`;
- `message`: `(sc_v: memory<bytes>) returns (Error)`,
  `return Error.Msg(memory(Typedef.rep(sc_v)));`;
- `pick`: `(sc_w: word, sc_a: Error, sc_b: Error) returns (Error)`, `sc_a`
  when its test of `sc_w` holds, otherwise `sc_b`;
- `call`: `(sc_e: Error, sc_w: word) returns (word)`,
  `return sc_h<j>(sc_e, (sc_w + c));` of an earlier `raise` or `call`
  helper. -/
inductive Helper where
  | raise (site : Site) (fold : Fold) (constant : Nat)
  | make (constant : Nat)
  | message
  | pick (test : Test)
  | call (callee constant : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `let sc_e<n>: Error = …;`: made in place, or by a `make`, `message` or
`pick` helper. -/
inductive Decl where
  | make (make : Make)
  | helper (helper : Nat) (word : Operand)
  | message (helper : Nat) (value : Nat)
  | pick (helper : Nat) (word : Operand) (first second : Source)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A data value of `run`: `(E, W)`, `inl(E)`, `inr(W)`,
`Sc_F.Sc_F0(E, W)` or `Sc_F.Sc_F1(W)`. -/
inductive Datum where
  | pair (error : Source) (word : Operand)
  | inl (error : Source)
  | inr (word : Operand)
  | first (error : Source) (word : Operand)
  | second (word : Operand)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A data variable: `sc_t<n>`, `sc_u<n>` or `sc_g<n>`. -/
inductive Held where
  | pair (number : Nat)
  | sum (number : Nat)
  | enum (number : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A loop body item: a `runtime-memory-values` action or a site. -/
inductive Item where
  | action (action : Action)
  | site (site : Site)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A step of `run`. A Word result is folded, `sc_r = ((sc_r * c) op …);`. -/
inductive Step where
  | action (action : Action)
  | error (decl : Decl)
  | data (datum : Datum)
  | site (site : Site)
  /-- `sc_h<k>(E, W)`, directly or through a function value. -/
  | call (helper : Nat) (error : Source) (word : Operand) (direct : Bool) (fold : Fold) (constant : Nat)
  /-- `match` of a data variable; the arm holding an `Error` has the site, an
  arm holding a Word folds it. -/
  | take (held : Held) (site : Site) (fold : Fold) (constant : Nat)
  /-- `lam (sc_j: word) -> word { SITE; return (sc_j op c); }`. -/
  | closure (site : Site) (fold : Fold) (constant : Nat)
  | apply (closure : Nat) (word : Operand) (fold : Fold) (constant : Nat)
  /-- `while (sc_limit > sc_counter)` with `sc_limit = (sc_x & mask)`. -/
  | loop (mask : Nat) (body : List Item)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Plan where
  helpers : List Helper
  steps : List Step
  deriving Repr, BEq, DecidableEq, Inhabited

/-! Bounds. -/

def maximumHelpers : Nat := 3
def maximumSteps : Nat := 12
def maximumErrors : Nat := 3
def maximumData : Nat := 2
def maximumClosures : Nat := 2
def maximumValues : Nat := 2
def maximumBody : Nat := 3
def maximumMessage : Nat := 64
def masks : List Nat := [1, 3, 7]
/-- Constants of `<` and `>`: boundary values and small counters. -/
def orderConstants : List Nat := [0, 1, 2, 3, 5, 255, 256, 1000, 2 ^ 255]
def equalConstants : List Nat := [0, 1, 2, 3, 255, 256]
def bitMasks : List Nat := [1, 2, 3, 7]

/-- The literals of `require(C, "…")` and `revertLit("…")`: 0 to 64 bytes;
`revertLit` admits those of at most 32, the most every lowering accepts. -/
def literals : List String := [
  "", "x", "no", "too large", "revert data",
  "abcdefghijklmnopqrstuvwxyz01234",
  "abcdefghijklmnopqrstuvwxyz012345",
  "abcdefghijklmnopqrstuvwxyz0123456",
  "the quick brown fox jumps over the lazy dog 0123456789 abcdefgh",
  "the quick brown fox jumps over the lazy dog 0123456789 abcdefghi"]

def literalLength (text : Nat) : Nat := ((literals[text]?).getD "").utf8ByteSize

def Test.admitted : Test → Bool
  | .lt constant | .gt constant => orderConstants.contains constant
  | .eq constant | .ne constant => equalConstants.contains constant
  | .bits mask value => bitMasks.contains mask && value ≤ mask

/-- A Word of a helper or closure: its parameter, with or without a
constant. -/
def isLocal : Operand → Bool
  | .input | .add _ | .mul _ | .xor _ => true
  | _ => false

def Fold.admitted (constant : Nat) : Bool := MemoryValues.foldConstants.contains constant

/-! The static scope. -/

/-- What an `Error` variable or the `Error` of a data value is: `selector`,
`empty`, `message` (with its bytes value), or `picked`. -/
inductive Kind where
  | selector
  | empty
  | message (object : Nat)
  | picked
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a data value holds: an `Error` of a kind, or a Word. -/
inductive Holds where
  | error (kind : Kind)
  | word
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Where a site is: `run` or its loop body, a helper, a closure or a match
arm holding an `Error`. -/
inductive Context where
  | run (inLoop : Bool)
  | helper
  | closure
  | arm (kind : Kind)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Env where
  scope : Scope := {}
  errors : List Kind := []
  pairs : List Holds := []
  sums : List Holds := []
  enums : List Holds := []
  closures : List (Site × Fold × Nat) := []
  values : Nat := 0
  loops : Nat := 0
  deriving Repr, BEq, Inhabited

private def need (condition : Bool) : Option Unit := if condition then some () else none

namespace Env

/-- A bytes variable that can be a message: in scope, at most 64 bytes. -/
def message? (env : Env) (value : Nat) : Option Var := do
  let var ← env.scope.var? (.bytes value)
  need (var.length ≤ maximumMessage)
  return var

def word? (inLoop : Bool) (context : Context) (word : Operand) : Bool :=
  match context with
  | .run _ => word.admitted inLoop
  | .arm _ => word.admitted false
  | .helper | .closure => isLocal word && word.admitted false

/-- The kind of an `Error` made in place. -/
def make? (env : Env) (context : Context) : Make → Option Kind
  | .selector word => do
      let inLoop := match context with
        | .run inLoop => inLoop
        | _ => false
      need (word? inLoop context word)
      return .selector
  | .empty => some .empty
  | .message value => do
      need (context != .helper)
      return .message (← env.message? value).object

/-- The kind of a source in a context. -/
def source? (env : Env) (context : Context) : Source → Option Kind
  | .make made => env.make? context made
  | .named number => do
      need (context != .helper)
      env.errors[number]?
  | .param => match context with
      | .helper => some .picked
      | .arm kind => some kind
      | _ => none

def site? (env : Env) (context : Context) (site : Site) : Bool :=
  let inLoop := match context with
    | .run inLoop => inLoop
    | _ => false
  word? inLoop context site.cond.word && site.cond.test.admitted &&
  match site.form, site.payload with
  | _, .error source => (env.source? context source).isSome
  | .when, .literal text => text < literals.length && literalLength text ≤ 32
  | .require, .literal text => text < literals.length
  | .when, .none => true
  | .require, .none => false

end Env

/-- A helper on its own: its site over its parameters, constants in range,
and a call of an earlier `raise` or `call` helper. -/
def Helper.admitted (helpers : List Helper) (index : Nat) : Helper → Bool
  | .raise site _ constant => Fold.admitted constant && ({} : Env).site? .helper site
  | .make constant => 1 ≤ constant && constant ≤ 255
  | .message => true
  | .pick test => test.admitted
  | .call callee constant =>
      callee < index && 1 ≤ constant && constant ≤ 255 &&
      match helpers[callee]? with
      | some (.raise ..) | some (.call ..) => true
      | _ => false

/-- The `raise` helper a call reaches, with the constants added on the way. -/
def resolve (helpers : List Helper) : Nat → Nat → Option (Site × Fold × Nat × Nat)
  | 0, _ => none
  | fuel + 1, index => do
      match ← helpers[index]? with
      | .raise site fold constant => return (site, fold, constant, 0)
      | .call callee constant => do
          let (site, fold, result, added) ← resolve helpers fuel callee
          return (site, fold, result, added + constant)
      | _ => none

def Helper.raises : Helper → Bool
  | .raise .. | .call .. => true
  | _ => false

namespace Env

def decl? (env : Env) (helpers : List Helper) : Decl → Option Kind
  | .make made => env.make? (.run false) made
  | .helper helper word => do
      need (word.admitted false)
      match ← helpers[helper]? with
      | .make _ => return .selector
      | _ => none
  | .message helper value => do
      match ← helpers[helper]? with
      | .message => return .message (← env.message? value).object
      | _ => none
  | .pick helper word first second => do
      need (word.admitted false)
      match ← helpers[helper]? with
      | .pick _ =>
          let _ ← env.source? (.run false) first
          let _ ← env.source? (.run false) second
          return .picked
      | _ => none

def datum? (env : Env) : Datum → Option Env
  | .pair error word => do
      need (word.admitted false && env.pairs.length < maximumData)
      return {env with pairs := env.pairs ++ [.error (← env.source? (.run false) error)]}
  | .inl error => do
      need (env.sums.length < maximumData)
      return {env with sums := env.sums ++ [.error (← env.source? (.run false) error)]}
  | .inr word => do
      need (word.admitted false && env.sums.length < maximumData)
      return {env with sums := env.sums ++ [.word]}
  | .first error word => do
      need (word.admitted false && env.enums.length < maximumData)
      return {env with enums := env.enums ++ [.error (← env.source? (.run false) error)]}
  | .second word => do
      need (word.admitted false && env.enums.length < maximumData)
      return {env with enums := env.enums ++ [.word]}

def held? (env : Env) : Held → Option Holds
  | .pair number => env.pairs[number]?
  | .sum number => env.sums[number]?
  | .enum number => env.enums[number]?

/-- The `runtime-memory-values` actions this profile admits: bytes values,
second variables, writes and observations of lengths, Words and bytes at
literal positions. -/
def Action.admitted : Action → Bool
  | .bytes (.toBytes part) => match part with
      | .value (.bytes _) | .word _ | .zeros _ => true
      | _ => false
  | .bytes (.concat left right) =>
      [left, right].all fun part => match part with
        | .value (.bytes _) | .word _ | .zeros _ => true
        | _ => false
  | .alias (.bytes _) => true
  | .write (.bytes _) (.literal _) _ _ _ => true
  | .observe _ _ (.bytes _) access => match access with
      | .length | .word (.literal _) | .byte (.literal _) => true
      | _ => false
  | _ => false

def action? (env : Env) (inLoop : Bool) (action : Action) : Option Env := do
  need (Action.admitted action)
  return {env with scope := ← env.scope.step? inLoop action}

def step? (env : Env) (helpers : List Helper) : Step → Option Env
  | .action action => env.action? false action
  | .error decl => do
      need (env.errors.length < maximumErrors)
      return {env with errors := env.errors ++ [← env.decl? helpers decl]}
  | .data datum => env.datum? datum
  | .site site => do
      need (env.site? (.run false) site)
      return env
  | .call helper error word direct _ constant => do
      need ((helpers[helper]?).any Helper.raises && word.admitted false && Fold.admitted constant)
      let _ ← env.source? (.run false) error
      need (direct || env.values < maximumValues)
      return {env with values := env.values + (if direct then 0 else 1)}
  | .take held site _ constant => do
      need (Fold.admitted constant)
      match ← env.held? held with
      | .error kind => need (env.site? (.arm kind) site)
      | .word => need (env.site? (.arm .selector) site)
      return env
  | .closure site fold constant => do
      need (Fold.admitted constant && env.closures.length < maximumClosures && env.site? .closure site)
      return {env with closures := env.closures ++ [(site, fold, constant)]}
  | .apply closure word _ constant => do
      need (closure < env.closures.length && word.admitted false && Fold.admitted constant)
      return env
  | .loop mask body => do
      need (masks.contains mask && env.loops = 0 && 1 ≤ body.length && body.length ≤ maximumBody)
      -- A body allocates and raises but neither reads nor writes a bytes value:
      -- such loops are Sonatina O0's recorded loop mismatches.
      let inner ← body.foldlM (fun (inner : Env) item => match item with
        | .action action => do
            need (action matches .bytes _)
            inner.action? true action
        | .site site => do
            need (inner.site? (.run true) site)
            return inner) env
      return {env with scope := inner.scope.close env.scope, loops := 1}

end Env

/-- The sites a step can reach: its own, a call's `raise` helper, a match
arm's, an application's closure, a loop's. -/
def Step.sites (helpers : List Helper) (env : Env) : Step → Nat
  | .site _ => 1
  | .call helper .. => if (resolve helpers (maximumHelpers + 1) helper).isSome then 1 else 0
  | .take held .. => match env.held? held with
      | some (.error _) => 1
      | _ => 0
  | .apply number .. => if number < env.closures.length then 1 else 0
  | .loop _ body => (body.filter fun item => match item with
      | .site _ => true
      | _ => false).length
  | _ => 0

/-- Whether a step folds a Word into `sc_r`. -/
def Step.folds (env : Env) : Step → Bool
  | .action (.observe ..) | .call .. | .apply .. => true
  | .take held .. =>
      let carries := match held with
        | .sum _ => false
        | _ => true
      match env.held? held with
      | some .word => true
      | _ => carries
  | .loop _ body => body.any fun item => match item with
      | .action (.observe ..) => true
      | _ => false
  | _ => false

namespace Plan

def scan? (plan : Plan) : Option (Env × Nat × Bool) :=
  plan.steps.foldlM (init := (({} : Env), 0, false)) fun (env, sites, folded) step => do
    let next ← env.step? plan.helpers step
    return (next, sites + step.sites plan.helpers env, folded || step.folds env)

/-- At least one site and one fold. -/
def admitted (plan : Plan) : Bool :=
  plan.helpers.length ≤ maximumHelpers &&
  plan.helpers.zipIdx.all (fun (helper, index) => helper.admitted plan.helpers index) &&
  1 ≤ plan.steps.length && plan.steps.length ≤ maximumSteps &&
  match plan.scan? with
  | some (_, sites, folded) => sites ≥ 1 && folded
  | none => false

end Plan

/-! The reference compiler. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def mul (left right : Expr) : Expr := .binary .wordMul left right
private def band (left right : Expr) : Expr := .binary .wordAnd left right
private def bxor (left right : Expr) : Expr := .binary .wordXor left right
private def shl (value shift : Expr) : Expr := .binary .wordShl value shift
private def gt (left right : Expr) : Expr := .binary .wordGt left right
private def eq (left right : Expr) : Expr := .binary .wordEq left right

/-- The revert payload: its length and its bytes in two Words, zero past
the length. -/
def payloadType : Ty := MemoryValues.words 3

def resultType : Ty := .sum .word payloadType

/-- The bytes of a literal packed into two Words. -/
def literalWord (text : Nat) (index : Nat) : Nat :=
  let bytes := ((literals[text]?).getD "").toUTF8.data.toList
  ((List.range 32).map fun offset => (bytes[32 * index + offset]?).getD 0).foldl (fun value byte => value * 256 + byte.toNat) 0

/-- An `Error` value of the reference: a selector at its bound Word, empty, a
message of a bytes value, or a choice by a bound condition. -/
inductive Desc where
  | selector (position : Nat)
  | empty
  | message (object length : Nat)
  | choice (condition : Nat) (first second : Desc)
  deriving Repr, BEq, Inhabited

def testExpr (word : Expr) : Test → Expr
  | .lt constant => gt (num constant) word
  | .gt constant => gt word (num constant)
  | .eq constant => eq word (num constant)
  | .ne constant => .unary .boolNot (eq word (num constant))
  | .bits mask value => eq (band word (num mask)) (num value)

def combine (fold : Fold) (left right : Expr) : Expr :=
  match fold with
  | .add => add left right
  | .xor => bxor left right

/-- A helper's or closure's Word over its bound parameter. -/
def localWord (state : State) (parameter : Nat) : Operand → Expr
  | .add constant => add (state.ref parameter) (num constant)
  | .mul constant => mul (state.ref parameter) (num constant)
  | .xor constant => bxor (state.ref parameter) (num constant)
  | _ => state.ref parameter

/-- The payload of an `Error` at a site: a message reads its value's Words
there. -/
def payloadOf (state : State) : Desc → Expr
  | .selector position => MemoryValues.packet [num 4, shl (state.ref position) (num 224), num 0]
  | .empty => MemoryValues.packet [num 0, num 0, num 0]
  | .message object length => MemoryValues.packet [num length, state.wordAt object 0, state.wordAt object 1]
  | .choice condition first second => .ifE (state.ref condition) (payloadOf state first) (payloadOf state second)

def literalPayload (text : Nat) : Expr :=
  MemoryValues.packet [num (literalLength text), num (literalWord text 0), num (literalWord text 1)]

/-- Revert with `payload` when `condition` holds: a bound sum that continues
or carries the payload, unpacked so that the scope forwards it. -/
def raise (state : State) (condition payload : Expr) : State :=
  let (state, flag) := state.bind (.ifE condition (.inRight .unit payload) (.inLeft payloadType .unit))
  (state.unpack (state.ref flag)).1

/-- How a site's Words and `sc_e` are read where it runs; a Word is read
through the state at its use. -/
structure Scene where
  word : State → Operand → Expr
  param : Option Desc := none

structure Compiler where
  state : State
  env : Env := {}
  errors : List Desc := []
  /-- The `Error` and Word of every pair, sum and enum value. -/
  pairs : List (Option Desc × Option Nat) := []
  sums : List (Option Desc × Option Nat) := []
  enums : List (Option Desc × Option Nat) := []

namespace Compiler

def make (errors : List Desc) (state : State) (word : State → Operand → Expr) : Make → State × Desc
  | .selector selector =>
      let (state, position) := state.bind (word state selector)
      (state, .selector position)
  | .empty => (state, .empty)
  | .message value => match state.scope.var? (.bytes value) with
      | some var => (state, .message var.object var.length)
      | none => let _ := errors; (state, .empty)

def source (errors : List Desc) (state : State) (scene : Scene) : Source → State × Desc
  | .make made => make errors state scene.word made
  | .named number => (state, errors.getD number .empty)
  | .param => (state, scene.param.getD .empty)

/-- A site where it runs: the payload's Words bound first, then the
condition read through the same state. -/
def site (errors : List Desc) (state : State) (scene : Scene) (site : Site) : State :=
  let (state, payload) := match site.payload with
    | .error origin =>
        let (state, desc) := source errors state scene origin
        (state, payloadOf state desc)
    | .literal text => (state, literalPayload text)
    | .none => (state, MemoryValues.packet [num 0, num 0, num 0])
  let condition := testExpr (scene.word state site.cond.word) site.cond.test
  let raising := match site.form with
    | .when => condition
    | .require => .unary .boolNot condition
  raise state raising payload

def runScene : Scene := {word := fun state => state.operand}

/-- A helper's or closure's scene over its bound parameter. -/
def localScene (parameter : Nat) (param : Option Desc) : Scene :=
  {word := fun state => localWord state parameter, param}

def fold (compiler : Compiler) (fold : Fold) (constant : Nat) (observed : Expr) : Compiler :=
  let state := compiler.state
  let (state, acc) := state.bind (combine fold (mul (state.ref state.acc) (num constant)) observed)
  {compiler with state := {state with acc}}

/-- A call of a `raise` or `call` helper, inlined: the Word bound once with the
constants added on the way, the helper's site over it, then its result. -/
def call (compiler : Compiler) (helpers : List Helper) (helper : Nat) (error : Source) (word : Operand) :
    Compiler × Option Expr := Id.run do
  let some (site, fold, constant, added) := resolve helpers (maximumHelpers + 1) helper | return (compiler, none)
  let state := compiler.state
  let (state, desc) := source compiler.errors state runScene error
  let (state, parameter) := state.bind (if added = 0 then state.operand word else add (state.operand word) (num added))
  let state := Compiler.site [] state (localScene parameter (some desc)) site
  return ({compiler with state}, some (combine fold (state.ref parameter) (num constant)))

/-- An `Error` declaration's value. -/
def decl (compiler : Compiler) (helpers : List Helper) : Decl → State × Desc
  | .make made => make compiler.errors compiler.state runScene.word made
  | .helper helper word =>
      let state := compiler.state
      let constant := match helpers[helper]? with
        | some (.make constant) => constant
        | _ => 0
      let (state, position) := state.bind (add (state.operand word) (num constant))
      (state, .selector position)
  | .message _ value => make compiler.errors compiler.state runScene.word (.message value)
  | .pick helper word first second =>
      let state := compiler.state
      let test := match helpers[helper]? with
        | some (.pick test) => test
        | _ => .eq 0
      let (state, firstDesc) := source compiler.errors state runScene first
      let (state, secondDesc) := source compiler.errors state runScene second
      let (state, condition) := state.bind (testExpr (state.operand word) test)
      (state, .choice condition firstDesc secondDesc)

def datum (compiler : Compiler) : Datum → Compiler
  | .pair error word =>
      let (state, desc) := source compiler.errors compiler.state runScene error
      let (state, position) := state.bind (state.operand word)
      {compiler with state, pairs := compiler.pairs ++ [(some desc, some position)]}
  | .inl error =>
      let (state, desc) := source compiler.errors compiler.state runScene error
      {compiler with state, sums := compiler.sums ++ [(some desc, none)]}
  | .inr word =>
      let (state, position) := compiler.state.bind (compiler.state.operand word)
      {compiler with state, sums := compiler.sums ++ [(none, some position)]}
  | .first error word =>
      let (state, desc) := source compiler.errors compiler.state runScene error
      let (state, position) := state.bind (state.operand word)
      {compiler with state, enums := compiler.enums ++ [(some desc, some position)]}
  | .second word =>
      let (state, position) := compiler.state.bind (compiler.state.operand word)
      {compiler with state, enums := compiler.enums ++ [(none, some position)]}

/-- A match arm runs where its data value's constructor is: the `Error` arm's
site, then a carried Word folded. -/
def take (compiler : Compiler) (held : Held) (site : Site) (fold : Fold) (constant : Nat) : Compiler :=
  let (desc, word) := match held with
    | .pair number => compiler.pairs.getD number (none, none)
    | .sum number => compiler.sums.getD number (none, none)
    | .enum number => compiler.enums.getD number (none, none)
  let compiler := match desc with
    | some desc =>
        let scene : Scene := {word := runScene.word, param := some desc}
        {compiler with state := Compiler.site compiler.errors compiler.state scene site}
    | none => compiler
  match word with
  | some position => compiler.fold fold constant (compiler.state.ref position)
  | none => compiler

def apply (compiler : Compiler) (closure : Site) (word : Operand) (constant : Nat) (closureFold : Fold) :
    Compiler × Expr :=
  let state := compiler.state
  let (state, parameter) := state.bind (state.operand word)
  let state := Compiler.site compiler.errors state (localScene parameter none) closure
  ({compiler with state}, combine closureFold (state.ref parameter) (num constant))

/-! The loop: `runtime-memory-values`' single loop, whose iterations return
the next state or forward a payload. -/

def iteration (state : State) (objects : List Nat) (body : State → State) : State × Nat :=
  let count := (state.components objects).length
  let stateType := MemoryValues.words count
  let outer := state.builder
  let parameter := outer.size
  let inner : State := {state with builder := {size := outer.size + 1}, abort := .inRight stateType (.var 0)}
  let (inner, position) := inner.bind (.first (inner.ref parameter))
  let (inner, source) := inner.bind (.second (inner.ref parameter))
  let (inner, positions) := inner.unpackState count source
  let inner := body {inner.restore objects positions with counter := some position}
  let result := Expr.inLeft payloadType (MemoryValues.packet ((inner.components objects).map inner.ref))
  let lambda := Expr.lambda (.product .word stateType) (.sum stateType payloadType)
    (inner.builder.close result inner.abort)
  {state with builder := outer, scope := inner.scope}.bind lambda

def chain (state : State) (stateType : Ty) (limit closure start trips : Nat) : State × Nat := Id.run do
  let mut state := state
  let mut current := start
  for ordinal in List.range trips do
    let under := fun (position : Nat) => Expr.var (state.builder.size - position)
    let (next, position) := state.bind (.caseE (state.ref current)
      (.ifE (gt (under limit) (num ordinal)) (.apply (under closure) (.pair (num ordinal) (.var 0)))
        (.inLeft payloadType (.var 0)))
      (.inRight stateType (.var 0)))
    state := next
    current := position
  return (state, current)

def loop (compiler : Compiler) (mask : Nat) (body : List Item) : Compiler :=
  let state := compiler.state
  let actions := body.filterMap fun item => match item with
    | .action action => some action
    | .site _ => none
  let objects := state.written actions
  let initial := state.components objects
  let count := initial.length
  let stateType := MemoryValues.words count
  let outerScope := state.scope
  let errors := compiler.errors
  let compileBody := fun (inner : State) => body.foldl (fun inner item => match item with
    | .action action => inner.action true action
    | .site site => Compiler.site errors inner runScene site) inner
  let (state, limit) := state.bind (band (state.ref state.input) (num mask))
  let (state, closure) := iteration state objects compileBody
  let (state, start) := state.bind (.inLeft payloadType (MemoryValues.packet (initial.map state.ref)))
  let (state, final) := chain state stateType limit closure start mask
  let (state, payload) := state.unpack (state.ref final)
  let (state, positions) := state.unpackState count payload
  let state := state.restore objects positions
  let scope := state.scope.close outerScope
  let values := state.values ++ Array.replicate (scope.objects.length - state.values.size) []
  {compiler with state := {state with scope, values, counter := none}}

/-- One step; the state's scope follows the environment's. -/
def step (compiler : Compiler) (helpers : List Helper) (step : Step) : Compiler :=
  let env := (compiler.env.step? helpers step).getD compiler.env
  let compiler := {compiler with state := {compiler.state with scope := compiler.env.scope}}
  let compiler : Compiler := match step with
  | .action action => {compiler with state := compiler.state.action false action}
  | .error decl =>
      let (state, desc) := compiler.decl helpers decl
      {compiler with state, errors := compiler.errors ++ [desc]}
  | .data datum => compiler.datum datum
  | .site site => {compiler with state := Compiler.site compiler.errors compiler.state runScene site}
  | .call helper error word _ fold constant =>
      match compiler.call helpers helper error word with
      | (compiler, some result) => compiler.fold fold constant result
      | (compiler, none) => compiler
  | .take held site fold constant => compiler.take held site fold constant
  | .closure .. => compiler
  | .apply closure word fold constant =>
      match compiler.env.closures[closure]? with
      | some (site, closureFold, closureConstant) =>
          let (compiler, result) := compiler.apply site word closureConstant closureFold
          compiler.fold fold constant result
      | none => compiler
  | .loop mask body => compiler.loop mask body
  {compiler with env, state := {compiler.state with scope := env.scope}}

end Compiler

namespace Plan

/-- `fun input => …`: the accumulator's zero, every step with its helpers and
closures inlined, then the left injection of the accumulator; a site's right
injection is forwarded by every scope. -/
def expression (plan : Plan) : Expr :=
  let state : State := {builder := {size := 1}, input := 0, abort := .inRight .word (.var 0)}
  let (state, acc) := state.bind (num 0)
  let compiler := plan.steps.foldl (fun compiler step => compiler.step plan.helpers step)
    ({state := {state with acc}} : Compiler)
  let state := compiler.state
  .lambda .word resultType (state.builder.close (.inLeft payloadType (state.ref state.acc)) state.abort)

def program (plan : Plan) : Program := {
  resultType := .function .word resultType, dataDefinitions := [], body := plan.expression}

def applied (plan : Plan) (input : Word) : Program := {
  resultType, dataDefinitions := [], body := .apply plan.expression (.word input)}

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

end Plan

/-! Specified shapes, from the plan. -/

def Site.formName (site : Site) : String :=
  match site.form, site.payload with
  | .when, .error _ => "revertWithError"
  | .require, .error _ => "require"
  | .when, .literal _ => "revertLit"
  | .require, .literal _ => "requireLiteral"
  | _, .none => "revertEmpty"

def Test.name : Test → String
  | .lt _ => "lt"
  | .gt _ => "gt"
  | .eq _ => "eq"
  | .ne _ => "ne"
  | .bits .. => "bits"

def Kind.name : Kind → String
  | .selector => "selector"
  | .empty => "empty"
  | .message _ => "message"
  | .picked => "picked"

def lengthClass (length : Nat) : String :=
  if length = 0 then "0" else if length < 32 then "1-31" else if length = 32 then "32"
  else if length < 64 then "33-63" else "64"

def Helper.name : Helper → String
  | .raise .. => "raise"
  | .make _ => "make"
  | .message => "message"
  | .pick _ => "pick"
  | .call .. => "call"

def Datum.name : Datum → String
  | .pair .. => "pair"
  | .inl _ => "inl"
  | .inr _ => "inr"
  | .first .. => "enum0"
  | .second _ => "enum1"

def Step.name : Step → String
  | .action _ => "action"
  | .error _ => "error"
  | .data _ => "data"
  | .site _ => "site"
  | .call .. => "call"
  | .take .. => "take"
  | .closure .. => "closure"
  | .apply .. => "apply"
  | .loop .. => "loop"

/-- An `Error` the trace follows: its kind, the payload lengths it can
revert with, and for a message its value and the trace's write and
allocation counts when it was made. -/
structure Made where
  kind : Kind
  lengths : List Nat
  written : Option (Nat × String × Nat × Nat) := none
  deriving Repr, BEq, Inhabited

structure Trace where
  shapes : List (String × String) := []
  /-- `(value, through)` of every write so far. -/
  writes : List (Nat × String) := []
  /-- Bytes values made so far. -/
  allocations : Nat := 0
  deriving Repr, Inhabited

def Trace.add (trace : Trace) (dimension value : String) : Trace :=
  {trace with shapes := trace.shapes ++ [(dimension, value)]}

def wordKind (context : Context) : Operand → String
  | .input => match context with
      | .helper | .closure => "local"
      | _ => "input"
  | .add _ | .mul _ | .xor _ => match context with
      | .helper | .closure => "local"
      | _ => "constant"
  | .acc => "acc"
  | .counter => "counter"

/-- A site's shapes, with the `Error` it raises. -/
def Trace.site (trace : Trace) (context : String) (word : String) (site : Site) (raised : Option (Made × String)) :
    Trace := Id.run do
  let mut trace := ((trace.add "forms" site.formName).add "contexts" context).add "tests" site.cond.test.name
  trace := trace.add "words" word
  match site.payload, raised with
  | .error _, some (made, carrier) =>
      trace := (trace.add "errors" made.kind.name).add "carriers" carrier
      for length in made.lengths do trace := trace.add "lengths" (lengthClass length)
      if let some (object, through, writes, allocations) := made.written then
        let later := trace.writes.drop writes
        if later.any (·.1 == object) then trace := trace.add "hazards" "written"
        if later.any (fun (written, writer) => written == object && writer != through) then trace := trace.add "hazards" "alias"
        if trace.allocations > allocations then trace := trace.add "hazards" "allocated"
  | .literal text, _ => trace := trace.add "lengths" (lengthClass (literalLength text))
  | .none, _ => trace := trace.add "lengths" "0"
  | _, _ => pure ()
  return trace

def refName : Ref → String
  | .bytes number => "sc_b" ++ toString number
  | .slice number => "sc_s" ++ toString number
  | .array number => "sc_a" ++ toString number

/-- The `Error` a source names, as the trace follows it. -/
def Trace.made (trace : Trace) (env : Env) (errors : List Made) (param : Option Made) (outer : Option Nat) :
    Source → Option (Made × String)
  | .make (.selector _) => some ({kind := .selector, lengths := [4]}, "inline")
  | .make .empty => some ({kind := .empty, lengths := [0]}, "inline")
  | .make (.message value) => do
      let _ := trace
      let var ← env.scope.var? (.bytes value)
      let fresh := outer.any (value ≥ ·)
      some ({kind := .message var.object, lengths := [var.length]}, if fresh then "loop" else "inline")
  | .named number => errors[number]?.map fun made => (made, "variable")
  | .param => param.map fun made => (made, "param")

def Plan.shapes (plan : Plan) : List (String × List String) := Id.run do
  let mut trace : Trace := {}
  let mut env : Env := {}
  let mut errors : List Made := []
  -- the `Error` each data value holds
  let mut held : List (List (Option Made)) := [[], [], []]
  let mut closures : List Nat := []
  for helper in plan.helpers do
    trace := trace.add "helpers" helper.name
  let makeMessage := fun (trace : Trace) (env : Env) (value : Nat) =>
    match env.scope.var? (.bytes value) with
    | some var =>
        let written := some (var.object, "sc_b" ++ toString value, trace.writes.length, trace.allocations)
        some ({kind := .message var.object, lengths := [var.length], written} : Made)
    | none => none
  for step in plan.steps do
    trace := trace.add "steps" step.name
    match step with
    | .action action =>
        match action with
        | .write target .. =>
            if let some var := env.scope.var? target then
              trace := {trace with writes := trace.writes ++ [(var.object, refName target)]}
        | .bytes _ => trace := {trace with allocations := trace.allocations + 1}
        | _ => pure ()
    | .error decl =>
        let made : Option Made := match decl with
          | .make (.selector _) => some {kind := .selector, lengths := [4]}
          | .make .empty => some {kind := .empty, lengths := [0]}
          | .make (.message value) => makeMessage trace env value
          | .helper .. => some {kind := .selector, lengths := [4]}
          | .message _ value => makeMessage trace env value
          | .pick _ _ first second =>
              let options := [first, second].filterMap fun source =>
                (trace.made env errors none none source).map (·.1)
              some {kind := .picked, lengths := options.flatMap (·.lengths)}
        let carrier := match decl with
          | .make _ => "variable"
          | .helper .. => "made"
          | .message .. => "messaged"
          | .pick .. => "picked"
        errors := errors ++ [made.getD {kind := .empty, lengths := [0]}]
        trace := trace.add "declarations" carrier
    | .data datum =>
        trace := trace.add "data" datum.name
        let of := fun (source : Source) => (trace.made env errors none none source).map (·.1)
        match datum with
        | .pair error _ => held := held.set 0 (held.getD 0 [] ++ [of error])
        | .inl error => held := held.set 1 (held.getD 1 [] ++ [of error])
        | .inr _ => held := held.set 1 (held.getD 1 [] ++ [none])
        | .first error _ => held := held.set 2 (held.getD 2 [] ++ [of error])
        | .second _ => held := held.set 2 (held.getD 2 [] ++ [none])
    | .site site =>
        trace := trace.site "run" (wordKind (.run false) site.cond.word) site
          (match site.payload with
            | .error source => trace.made env errors none none source
            | _ => none)
    | .call helper error _ direct _ _ =>
        let chainLength := (List.range (maximumHelpers + 1)).foldl (fun (current, length) _ =>
          match plan.helpers[current]? with
          | some (.call callee _) => (callee, length + 1)
          | _ => (current, length)) (helper, 0)
        let passed := (trace.made env errors none none error).map (·.1)
        if let some (site, _, _, _) := resolve plan.helpers (maximumHelpers + 1) helper then
          trace := trace.site (if chainLength.2 > 0 then "call" else "helper") (wordKind .helper site.cond.word) site
            (match site.payload with
              | .error .param => passed.map fun made => (made, if direct then "passed" else "value")
              | .error source => trace.made env errors none none source
              | _ => none)
    | .take target site _ _ =>
        let (kind, number) := match target with
          | .pair number => (0, number)
          | .sum number => (1, number)
          | .enum number => (2, number)
        let name := match target with
          | .pair _ => "pair"
          | .sum _ => "sum"
          | .enum _ => "enum"
        if let some (some made) := (held.getD kind [])[number]? then
          trace := trace.site name (wordKind (.arm made.kind) site.cond.word) site
            (match site.payload with
              | .error .param => some (made, "held")
              | .error source => trace.made env errors none none source
              | _ => none)
    | .closure .. => closures := closures ++ [trace.writes.length]
    | .apply number .. =>
        if let some (site, _, _) := env.closures[number]? then
          trace := trace.site "closure" (wordKind .closure site.cond.word) site
            (match site.payload with
              | .error (.named number) => errors[number]?.map fun made => (made, "captured")
              | .error source => trace.made env errors none none source
              | _ => none)
    | .loop _ body =>
        let mut inner := env
        let outer := env.scope.bytes.length
        for item in body do
          match item with
          | .action action =>
              match action with
              | .write target .. =>
                  if let some var := inner.scope.var? target then
                    trace := {trace with writes := trace.writes ++ [(var.object, refName target)]}
              | .bytes _ => trace := {trace with allocations := trace.allocations + 1}
              | _ => pure ()
              inner := (inner.action? true action).getD inner
          | .site site =>
              trace := trace.site "loop" (wordKind (.run true) site.cond.word) site
                (match site.payload with
                  | .error source => trace.made inner errors none (some outer) source
                  | _ => none)
    env := (env.step? plan.helpers step).getD env
  let sorted := fun (values : List String) => values.eraseDups.mergeSort (· ≤ ·)
  let of := fun (dimension : String) => sorted (trace.shapes.filterMap fun (name, value) =>
    if name == dimension then some value else none)
  return [("helpers", of "helpers"), ("forms", of "forms"), ("errors", of "errors"),
    ("contexts", of "contexts"), ("carriers", of "carriers"), ("declarations", of "declarations"),
    ("data", of "data"), ("tests", of "tests"), ("words", of "words"), ("lengths", of "lengths"),
    ("hazards", of "hazards"), ("steps", of "steps")]

/-! Generation. -/

def domain : UInt64 := 0x7265766572740001

private def pick {α : Type} [Inhabited α] (values : List α) : Gen α := do
  return values[← draw values.length]!

def drawFold : Gen Fold := do return if (← draw 2) = 0 then .add else .xor

/-- A test that holds for few inputs when it raises (`if`) and for most when
it must hold (`require`); a loop's counter takes small constants. -/
def drawTest (raises : Bool) (counter : Bool) : Gen Test := do
  let bits : Gen Test := do
    let mask ← pick bitMasks
    return .bits mask (← draw (mask + 1))
  if counter then
    let choice ← draw 2
    if raises then
      if choice = 0 then return .eq (← pick [0, 1, 2, 3]) else return .gt (← pick [1, 2, 3])
    if choice = 0 then return .ne (← pick [0, 1, 2, 3]) else return .lt (← pick [2, 3, 5])
  if raises then
    match ← drawWeighted [3, 2, 1, 3] with
    | 0 => return .eq (← pick equalConstants)
    | 1 => return .gt (← pick [255, 256, 1000, 2 ^ 255])
    | 2 => return .lt (← pick [1, 2, 3])
    | _ => return (← bits)
  match ← drawWeighted [3, 2, 1, 2] with
  | 0 => return .ne (← pick equalConstants)
  | 1 => return .lt (← pick [255, 256, 1000, 2 ^ 255])
  | 2 => return .gt (← pick [0, 1, 2])
  | _ => bits

def drawLocal : Gen Operand := do
  match ← drawWeighted [4, 1, 1, 1] with
  | 0 => return .input
  | 1 => return .add (1 + (← draw 255))
  | 2 => return .mul (2 + (← draw 254))
  | _ => return .xor (1 + (← draw 255))

/-- A tested Word: mostly the input, rarely the accumulator. -/
def drawTested : Gen Operand := do
  match ← drawWeighted [6, 1, 1, 1, 1] with
  | 0 => return .input
  | 1 => return .add (1 + (← draw 255))
  | 2 => return .mul (2 + (← draw 254))
  | 3 => return .xor (1 + (← draw 255))
  | _ => return .acc

def drawWord (context : Context) : Gen Operand := do
  match context with
  | .run inLoop => MemoryValues.drawOperand inLoop
  | .arm _ => MemoryValues.drawOperand false
  | .helper | .closure => drawLocal

/-- The bytes variables in scope that can be messages. -/
def Env.messages (env : Env) : List Nat :=
  (List.range env.scope.bytes.length).filter fun value => (env.message? value).isSome

def drawMake (env : Env) (context : Context) (outer : Nat := 0) : Gen Make := do
  let messages := if context == .helper then [] else env.messages
  let own := messages.filter (· ≥ outer)
  match ← drawWeighted [3, 1, if messages.isEmpty then 0 else 3] with
  | 0 => return .selector (← drawWord context)
  | 1 => return .empty
  | _ => return .message (← if context == .run true && !own.isEmpty && (← draw 2) = 0 then pick own else pick messages)

def drawSource (env : Env) (context : Context) (outer : Nat := 0) : Gen Source := do
  let variables := if context == .helper then 0 else env.errors.length
  let param := match context with
    | .helper | .arm _ => true
    | _ => false
  let named := if variables = 0 then 0 else if context == .closure then 6 else 3
  match ← drawWeighted [2, named, if param then 5 else 0] with
  | 0 => return .make (← drawMake env context outer)
  | 1 => return .named (← draw variables)
  | _ => return .param

def drawSite (env : Env) (context : Context) (outer : Nat := 0) : Gen Site := do
  let counter := context == .run true && (← draw 3) != 0
  let word ← if counter then pure Operand.counter else match context with
    | .helper | .closure => drawLocal
    | _ => drawTested
  let shape ← drawWeighted [3, 3, 2, 2, 1]
  let form := if shape = 1 || shape = 3 then Form.require else .when
  let cond : Cond := {word, test := ← drawTest (form == .when) counter}
  match shape with
  | 0 | 1 => return {form, cond, payload := .error (← drawSource env context outer)}
  | 2 => return {form, cond, payload := .literal (← pick ((List.range literals.length).filter fun text =>
      literalLength text ≤ 32))}
  | 3 => return {form, cond, payload := .literal (← draw literals.length)}
  | _ => return {form, cond, payload := .none}

def drawHelper (helpers : List Helper) : Gen Helper := do
  let raising := (List.range helpers.length).filter fun index => (helpers[index]?).any Helper.raises
  match ← drawWeighted [4, 2, 2, 2, if raising.isEmpty then 0 else 3] with
  | 0 => return .raise (← drawSite {} .helper) (← drawFold) (← pick MemoryValues.foldConstants)
  | 1 => return .make (1 + (← draw 255))
  | 2 => return .message
  | 3 => return .pick (← drawTest true false)
  | _ => return .call (← pick raising) (1 + (← draw 255))

/-- A bytes value built from Words and zeros, at most 64 bytes half the time
so that it can be a message. -/
def drawBuild (env : Env) (inLoop : Bool) : Gen Action := do
  let word ← MemoryValues.drawOperand inLoop
  let values := (List.range env.scope.bytes.length).filter fun value =>
    (env.scope.var? (.bytes value)).any (·.length ≤ 96)
  match ← drawWeighted [3, 3, 2, if values.isEmpty then 0 else 2] with
  | 0 => return .bytes (.toBytes (.word word))
  | 1 => return .bytes (.concat (.word word) (.word (← MemoryValues.drawOperand inLoop)))
  | 2 => return .bytes (.concat (.word word) (.zeros (1 + (← draw 32))))
  | _ => return .bytes (.concat (.value (.bytes (← pick values))) (.zeros (← draw 9)))

/-- A write into, or an observation of, a bytes variable at a literal
position, or a second variable. -/
def drawAction (env : Env) (inLoop : Bool) : Gen (Option Action) := do
  let values := (List.range env.scope.bytes.length).filter fun value => (env.scope.var? (.bytes value)).isSome
  if values.isEmpty || (← draw 4) = 0 then return some (← drawBuild env inLoop)
  let value ← pick values
  let var := (env.scope.var? (.bytes value)).getD default
  match ← drawWeighted [4, 3, if inLoop then 0 else 1] with
  | 0 =>
      let width ← if 32 ≤ var.length && (← draw 2) = 0 then pure Width.word else pure Width.byte
      if var.length = 0 then return none
      let valid := (width.valid? var.length).getD 1
      let form := if (← draw 2) = 0 then MemoryValues.Form.inline else .helper
      return some (.write (.bytes value) (.literal (← draw valid)) (← MemoryValues.drawOperand inLoop) width form)
  | 1 =>
      let access ← match ← drawWeighted [2, if 32 ≤ var.length then 2 else 0, if 1 ≤ var.length then 2 else 0] with
        | 0 => pure MemoryValues.Access.length
        | 1 => pure (.word (.literal (← draw (var.length - 31))))
        | _ => pure (.byte (.literal (← draw var.length)))
      return some (.observe (← drawFold) (← pick MemoryValues.foldConstants) (.bytes value) access)
  | _ => return some (.alias (.bytes value))

def drawDecl (env : Env) (helpers : List Helper) : Gen Decl := do
  let of := fun (wanted : Helper → Bool) => (List.range helpers.length).filter fun index => (helpers[index]?).any wanted
  let makers := of fun helper => helper matches .make _
  let messengers := if env.messages.isEmpty then [] else of fun helper => helper matches .message
  let pickers := of fun helper => helper matches .pick _
  match ← drawWeighted [3, if makers.isEmpty then 0 else 3, if messengers.isEmpty then 0 else 3,
      if pickers.isEmpty then 0 else 3] with
  | 0 => return Decl.make (← drawMake env (.run false))
  | 1 => return Decl.helper (← pick makers) (← MemoryValues.drawOperand false)
  | 2 => return Decl.message (← pick messengers) (← pick env.messages)
  | _ =>
      let helper ← pick pickers
      let word ← MemoryValues.drawOperand false
      let first ← drawSource env (.run false)
      return Decl.pick helper word first (← drawSource env (.run false))

def drawDatum (env : Env) : Gen Datum := do
  let error ← drawSource env (.run false)
  let word ← MemoryValues.drawOperand false
  match ← drawWeighted [3, 2, 2, 2, 2] with
  | 0 => return .pair error word
  | 1 => return .inl error
  | 2 => return .inr word
  | 3 => return .first error word
  | _ => return .second word

def drawHeld (env : Env) : Gen (Option Held) := do
  let candidates := (List.range env.pairs.length).map Held.pair ++ (List.range env.sums.length).map Held.sum ++
    (List.range env.enums.length).map Held.enum
  if candidates.isEmpty then return none
  return some (← pick candidates)

/-- One step the environment admits, by weights that favour sites and calls. -/
def drawStep (env : Env) (helpers : List Helper) : Gen (Option Step) := do
  let raising := (List.range helpers.length).filter fun index => (helpers[index]?).any Helper.raises
  let data := env.pairs.length + env.sums.length + env.enums.length
  let weights := [4, if env.errors.length < maximumErrors then 3 else 0, 2, 4,
    if raising.isEmpty then 0 else 4, if data = 0 then 0 else 3,
    if env.closures.length < maximumClosures then 2 else 0, if env.closures.isEmpty then 0 else 3,
    if env.loops = 0 then 2 else 0]
  match ← drawWeighted weights with
  | 0 => return (← drawAction env false).map Step.action
  | 1 => return some (.error (← drawDecl env helpers))
  | 2 => return some (.data (← drawDatum env))
  | 3 => return some (.site (← drawSite env (.run false)))
  | 4 =>
      let helper ← pick raising
      return some (.call helper (← drawSource env (.run false)) (← MemoryValues.drawOperand false) ((← draw 3) != 0)
        (← drawFold) (← pick MemoryValues.foldConstants))
  | 5 =>
      let some held ← drawHeld env | return none
      let kind : Context := match env.held? held with
        | some (.error kind) => .arm kind
        | _ => .arm .selector
      return some (.take held (← drawSite env kind) (← drawFold) (← pick MemoryValues.foldConstants))
  | 6 => return some (.closure (← drawSite env .closure) (← drawFold) (← pick MemoryValues.foldConstants))
  | 7 => return some (.apply (← draw env.closures.length) (← MemoryValues.drawOperand false) (← drawFold)
      (← pick MemoryValues.foldConstants))
  | _ =>
      let mask ← pick masks
      let count := 1 + (← draw maximumBody)
      let mut inner := env
      let mut body : List Item := []
      let mut site := false
      for position in List.range count do
        if !site && (position + 1 = count || (← draw 2) = 0) then
          let drawn ← drawSite inner (.run true) env.scope.bytes.length
          if inner.site? (.run true) drawn then
            body := body ++ [.site drawn]
            site := true
            continue
        let action ← drawBuild inner true
        if let some next := inner.action? true action then
          body := body ++ [.action action]
          inner := next
      return some (.loop mask body)

/-- Up to three helpers, one or two bytes values, then steps drawn by weight;
each is kept when admitted. A plan without a site or a fold ends with one. -/
def drawPlan : Gen Plan := do
  let count ← draw (maximumHelpers + 1)
  let mut helpers : List Helper := []
  for index in List.range count do
    let helper ← drawHelper helpers
    if helper.admitted helpers index then helpers := helpers ++ [helper]
  let mut env : Env := {}
  let mut steps : List Step := []
  for _ in List.range (1 + (← draw 2)) do
    let action ← drawBuild env false
    if let some next := env.step? helpers (.action action) then
      env := next
      steps := steps ++ [.action action]
  if (← draw 3) = 0 then
    if let some value := env.messages.head? then
      let messenger := (List.range helpers.length).find? fun index => (helpers[index]?).any (· matches .message)
      let viaHelper := (← draw 2) = 0
      let decl := match messenger with
        | some helper => if viaHelper then Decl.message helper value else .make (.message value)
        | none => Decl.make (.message value)
      let var := (env.scope.var? (.bytes value)).getD default
      let write := fun (target : Nat) => Step.action (.write (.bytes target) (.literal (var.length / 2))
        .input .byte .inline)
      let hazard ← match ← draw 3 with
        | 0 => pure [write value]
        | 1 => pure [.action (.alias (.bytes value)), write env.scope.bytes.length]
        | _ => pure [.action (← drawBuild env false)]
      let test ← drawTest true false
      let raise : Step := .site {form := .when, cond := {word := .input, test}, payload := .error (.named env.errors.length)}
      for step in [.error decl] ++ hazard ++ [raise] do
        if let some next := env.step? helpers step then
          env := next
          steps := steps ++ [step]
  let total := steps.length + 2 + (← draw (maximumSteps - 4))
  for _ in List.range (4 * total) do
    if steps.length ≥ min total maximumSteps then break
    if let some step ← drawStep env helpers then
      if let some next := env.step? helpers step then
        env := next
        steps := steps ++ [step]
  let plan : Plan := {helpers, steps}
  if plan.admitted then return plan
  let mut kept := steps.take (maximumSteps - 2)
  let mut last : Env := ((({helpers, steps := kept} : Plan).scan?).map (·.1)).getD {}
  let site ← drawSite last (.run false)
  if last.site? (.run false) site then
    kept := kept ++ [.site site]
    last := (last.step? helpers (.site site)).getD last
  if let some value := (List.range last.scope.bytes.length).find? fun value => (last.scope.var? (.bytes value)).isSome then
    kept := kept ++ [.action (.observe .add 3 (.bytes value) .length)]
  return {helpers, steps := kept}

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- Steps are dropped from the end while the reference exceeds `nodes`, more
than one step remains and the rest is still admitted. -/
def Plan.fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.steps.length do
    let shorter : Plan := {plan with steps := plan.steps.dropLast}
    if plan.nodes > nodes && plan.steps.length > 1 && shorter.admitted then
      plan := shorter
  return plan

end Solcore.Synthesis.Core.RevertData
