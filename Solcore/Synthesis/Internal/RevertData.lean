import Solcore.Synthesis.Internal.MemoryValues

/-!
# Profiles: revert data and halts

The profiles `runtime-revert-data` and `runtime-halts`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.RevertData
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
source text.

`runtime-halts` shares these plans with a fifth kind of site, which halts with
INVALID through `assert`, std.opcodes' `invalid()` or inline Yul; it raises
the right injection with a length no revert data has. Its plans are admitted,
drawn, shaped and reduced here too, and a revert data plan admits no halt. -/
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

/-- How a `runtime-halts` site halts with INVALID: std's `assert(C);`, which
halts when `C` does not hold, or `if (C) { invalid(); }` through
std.opcodes' `invalid()`, `if (C) { assembly { invalid() } }`, or
`assembly { if C { invalid() } }` with `C` in Yul. -/
inductive Halt where
  | assert
  | opcode
  | inline
  | yul
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a site reverts with: an `Error`, a literal, or nothing; or the halt
of a `runtime-halts` site. -/
inductive Payload where
  | error (source : Source)
  | literal (text : Nat)
  | none
  | halt (halt : Halt)
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
  | .require, .halt halt => halt == .assert
  | .when, .halt halt => halt != .assert

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

def Site.halts (site : Site) : Bool := site.payload matches .halt _

def Helper.halts : Helper → Bool
  | .raise site .. => site.halts
  | _ => false

def Step.halts : Step → Bool
  | .site single | .take _ single .. | .closure single .. => single.halts
  | .loop _ body => body.any fun item => match item with
      | .site single => single.halts
      | _ => false
  | _ => false

/-- The halt sites a step can reach, as `Step.sites` counts sites. -/
def Step.haltSites (helpers : List Helper) (env : Env) : Step → Nat
  | .site single => if single.halts then 1 else 0
  | .call helper .. => match resolve helpers (maximumHelpers + 1) helper with
      | some (single, _) => if single.halts then 1 else 0
      | none => 0
  | .take held single .. => match env.held? held with
      | some (.error _) => if single.halts then 1 else 0
      | _ => 0
  | .apply number .. => match env.closures[number]? with
      | some (single, _) => if single.halts then 1 else 0
      | none => 0
  | .loop _ body => (body.filter fun item => match item with
      | .site single => single.halts
      | _ => false).length
  | _ => 0

namespace Plan

def scan? (plan : Plan) : Option (Env × Nat × Bool) :=
  plan.steps.foldlM (init := (({} : Env), 0, false)) fun (env, sites, folded) step => do
    let next ← env.step? plan.helpers step
    return (next, sites + step.sites plan.helpers env, folded || step.folds env)

def halts (plan : Plan) : Bool := plan.helpers.any Helper.halts || plan.steps.any Step.halts

/-- At least one site and one fold. -/
def admittedSteps (plan : Plan) : Bool :=
  plan.helpers.length ≤ maximumHelpers &&
  plan.helpers.zipIdx.all (fun (helper, index) => helper.admitted plan.helpers index) &&
  1 ≤ plan.steps.length && plan.steps.length ≤ maximumSteps &&
  match plan.scan? with
  | some (_, sites, folded) => sites ≥ 1 && folded
  | none => false

/-- A `runtime-revert-data` plan: no site halts. -/
def admitted (plan : Plan) : Bool := !plan.halts && plan.admittedSteps

/-- The halt sites the plan's steps can reach. -/
def reachedHalts (plan : Plan) : Nat :=
  (plan.steps.foldl (init := (({} : Env), 0)) fun (env, halts) step =>
    ((env.step? plan.helpers step).getD env, halts + step.haltSites plan.helpers env)).2

/-- A `runtime-halts` plan: a halt site it can reach. -/
def haltAdmitted (plan : Plan) : Bool := plan.admittedSteps && plan.reachedHalts ≥ 1

def admittedFor (halts : Bool) (plan : Plan) : Bool := if halts then plan.haltAdmitted else plan.admitted

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

/-- A halt's length, which no revert data has: the right injection of a
`runtime-halts` reference with this length and no bytes is INVALID's halt. -/
def haltLength : Nat := 2 ^ 256 - 1

def haltPayload : Expr := MemoryValues.packet [num haltLength, num 0, num 0]

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
    | .halt _ => (state, haltPayload)
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
  let inner : State := {state with builder := {size := outer.size + 1}, left := stateType}
  let (inner, position) := inner.bind (.first (inner.ref parameter))
  let (inner, source) := inner.bind (.second (inner.ref parameter))
  let (inner, positions) := inner.unpackState count source
  let inner := body {inner.restore objects positions with counter := some position}
  let result := Expr.inLeft payloadType (MemoryValues.packet ((inner.components objects).map inner.ref))
  let lambda := Expr.lambda (.product .word stateType) (.sum stateType payloadType)
    (inner.builder.close result inner.left)
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
  let state : State := {builder := {size := 1}, input := 0, left := .word}
  let (state, acc) := state.bind (num 0)
  let compiler := plan.steps.foldl (fun compiler step => compiler.step plan.helpers step)
    ({state := {state with acc}} : Compiler)
  let state := compiler.state
  .lambda .word resultType (state.builder.close (.inLeft payloadType (state.ref state.acc)) state.left)

def program (plan : Plan) : Program := {
  resultType := .function .word resultType, dataDefinitions := [], body := plan.expression}

def applied (plan : Plan) (input : Word) : Program := {
  resultType, dataDefinitions := [], body := .apply plan.expression (.word input)}

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

end Plan

/-! Specified shapes, from the plan. -/

def Halt.name : Halt → String
  | .assert => "assert"
  | .opcode => "invalid"
  | .inline => "inline"
  | .yul => "yul"

def Site.formName (site : Site) : String :=
  match site.form, site.payload with
  | .when, .error _ => "revertWithError"
  | .require, .error _ => "require"
  | .when, .literal _ => "revertLit"
  | .require, .literal _ => "requireLiteral"
  | _, .none => "revertEmpty"
  | _, .halt halt => halt.name

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
  /-- Every site in the order it runs: whether it halts, and the writes before
  it. -/
  visits : List (Bool × Nat) := []
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

/-- A site's shapes, with the `Error` it raises; a halt site's are its own. -/
def Trace.site (trace : Trace) (context : String) (word : String) (site : Site) (raised : Option (Made × String)) :
    Trace := Id.run do
  let trace := {trace with visits := trace.visits ++ [(site.halts, trace.writes.length)]}
  if site.halts then
    return (((trace.add "halts" site.formName).add "haltContexts" context).add "haltTests" site.cond.test.name).add
      "haltWords" word
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

/-- Every site a plan's steps run, in order, with the shapes they record. -/
def Plan.trace (plan : Plan) : Trace := Id.run do
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
  return trace

def Trace.of (trace : Trace) (dimension : String) : List String :=
  (trace.shapes.filterMap fun (name, value) => if name == dimension then some value else none).eraseDups.mergeSort
    (· ≤ ·)

def Plan.shapes (plan : Plan) : List (String × List String) :=
  let trace := plan.trace
  ["helpers", "forms", "errors", "contexts", "carriers", "declarations", "data", "tests", "words", "lengths",
    "hazards", "steps"].map fun dimension => (dimension, trace.of dimension)

/-- Where halt sites run: after a revert site, before one, after a write, and
before one. -/
def Trace.orders (trace : Trace) : List String :=
  let visits := trace.visits.zipIdx
  let halts := visits.filter (·.1.1)
  let reverts := visits.filter (!·.1.1)
  let writes := trace.writes.length
  (if halts.any (fun (_, position) => reverts.any (·.2 < position)) then ["revert-before"] else []) ++
  (if halts.any (fun (_, position) => reverts.any (·.2 > position)) then ["revert-after"] else []) ++
  (if halts.any (·.1.2 > 0) then ["write-before"] else []) ++
  (if halts.any (·.1.2 < writes) then ["write-after"] else [])

/-- The `runtime-halts` shapes: halt forms, contexts, tests and tested Words,
and orders. -/
def Plan.haltShapes (plan : Plan) : List (String × List String) :=
  let trace := plan.trace
  ["halts", "haltContexts", "haltTests", "haltWords"].map (fun dimension => (dimension, trace.of dimension)) ++
    [("haltOrders", trace.orders.mergeSort (· ≤ ·))]

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

/-- A halt site of `runtime-halts`: each form equally, `assert` with a test
that holds for most inputs and the others with one that holds for few. -/
def drawHalt (context : Context) : Gen Site := do
  let counter := context == .run true && (← draw 3) != 0
  let word ← if counter then pure Operand.counter else match context with
    | .helper | .closure => drawLocal
    | _ => drawTested
  let halt ← pick [Halt.assert, .opcode, .inline, .yul]
  let form := if halt == .assert then Form.require else .when
  return {form, cond := {word, test := ← drawTest (form == .when) counter}, payload := .halt halt}

/-- A site; with `halts`, half the time a halt site. -/
def drawSite (env : Env) (context : Context) (outer : Nat := 0) (halts : Bool := false) : Gen Site := do
  if halts then
    -- Nested, so that a revert data plan draws exactly what it drew before.
    if (← draw 2) = 0 then return ← drawHalt context
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

def drawHelper (helpers : List Helper) (halts : Bool := false) : Gen Helper := do
  let raising := (List.range helpers.length).filter fun index => (helpers[index]?).any Helper.raises
  match ← drawWeighted [4, 2, 2, 2, if raising.isEmpty then 0 else 3] with
  | 0 => return .raise (← drawSite {} .helper (halts := halts)) (← drawFold) (← pick MemoryValues.foldConstants)
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
def drawStep (env : Env) (helpers : List Helper) (halts : Bool := false) : Gen (Option Step) := do
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
  | 3 => return some (.site (← drawSite env (.run false) (halts := halts)))
  | 4 =>
      let helper ← pick raising
      return some (.call helper (← drawSource env (.run false)) (← MemoryValues.drawOperand false) ((← draw 3) != 0)
        (← drawFold) (← pick MemoryValues.foldConstants))
  | 5 =>
      let some held ← drawHeld env | return none
      let kind : Context := match env.held? held with
        | some (.error kind) => .arm kind
        | _ => .arm .selector
      return some (.take held (← drawSite env kind (halts := halts)) (← drawFold) (← pick MemoryValues.foldConstants))
  | 6 => return some (.closure (← drawSite env .closure (halts := halts)) (← drawFold)
      (← pick MemoryValues.foldConstants))
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
          let drawn ← drawSite inner (.run true) env.scope.bytes.length halts
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
each is kept when admitted. A plan without a site or a fold ends with one;
with `halts`, a plan without a halt site it reaches ends with a halt site. -/
def drawPlan (halts : Bool := false) : Gen Plan := do
  let count ← draw (maximumHelpers + 1)
  let mut helpers : List Helper := []
  for index in List.range count do
    let helper ← drawHelper helpers halts
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
    if let some step ← drawStep env helpers halts then
      if let some next := env.step? helpers step then
        env := next
        steps := steps ++ [step]
  let plan : Plan := {helpers, steps}
  if plan.admittedFor halts then return plan
  let mut kept := steps.take (maximumSteps - 2)
  let mut last : Env := ((({helpers, steps := kept} : Plan).scan?).map (·.1)).getD {}
  let site ← if halts then drawHalt (.run false) else drawSite last (.run false)
  if last.site? (.run false) site then
    kept := kept ++ [.site site]
    last := (last.step? helpers (.site site)).getD last
  if let some value := (List.range last.scope.bytes.length).find? fun value => (last.scope.var? (.bytes value)).isSome then
    kept := kept ++ [.action (.observe .add 3 (.bytes value) .length)]
  return {helpers, steps := kept}

def generate (seed : UInt64) : Plan :=
  (drawPlan.run {seed, domain, index := 0}).1

/-- `runtime-halts`' own stream. -/
def haltDomain : UInt64 := 0x68616c7400000001

def generateHalts (seed : UInt64) : Plan :=
  ((drawPlan (halts := true)).run {seed, domain := haltDomain, index := 0}).1

/-- Steps are dropped from the end while the reference exceeds `nodes`, more
than one step remains and the rest is still admitted. -/
def Plan.fit (nodes : Nat) (plan : Plan) (halts : Bool := false) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range plan.steps.length do
    let shorter : Plan := {plan with steps := plan.steps.dropLast}
    if plan.nodes > nodes && plan.steps.length > 1 && shorter.admittedFor halts then
      plan := shorter
  return plan

end Solcore.Synthesis.Core.RevertData
end

section
-- leanmerge: from Solcore.Synthesis.Core.RevertDataShrink
/-! The plan size of a revert data plan and its reductions. A call weighs 20,
more than any site step, at most 19, so replacing a call by the site it
reaches is smaller; a reduction is kept only when strictly smaller. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.RevertData

open Solcore.Synthesis.Core.MemoryValues (Operand Index Ref Width Fold Part Build Action)

def operandSize : Operand → Nat
  | .input => 0
  | .acc | .counter => 1
  | .add constant | .mul constant | .xor constant => 1 + (if constant = 1 then 0 else 1)

def constantSize (constant : Nat) : Nat := if constant = 0 then 0 else if constant ≤ 3 then 1 else 2

def Test.size : Test → Nat
  | .eq constant => constantSize constant
  | .ne constant | .lt constant | .gt constant => 1 + constantSize constant
  | .bits mask value => 1 + constantSize mask + constantSize value

def Make.size : Make → Nat
  | .empty => 1
  | .selector word => 2 + operandSize word
  | .message _ => 3

def Source.size : Source → Nat
  | .make made => made.size
  | .named _ | .param => 2

/-- A halt: `assert` and inline Yul under `if` weigh nothing, a call of
std.opcodes' `invalid()` and a Yul `if` one. -/
def Halt.size : Halt → Nat
  | .assert | .inline => 0
  | .opcode | .yul => 1

def Payload.size : Payload → Nat
  | .none => 0
  | .literal text => 1 + text
  | .error origin => 1 + origin.size
  | .halt kind => kind.size

def Site.size (site : Site) : Nat :=
  1 + (if site.form == .require then 1 else 0) + operandSize site.cond.word + site.cond.test.size + site.payload.size

def foldSize (fold : Fold) (constant : Nat) : Nat := (if fold == .xor then 1 else 0) + (if constant = 3 then 0 else 1)

def actionSize : Action → Nat
  | .bytes (.toBytes _) => 2
  | .bytes (.concat ..) => 3
  | .alias _ => 2
  | .write .. => 3
  | .observe .. => 3
  | _ => 3

def Helper.size : Helper → Nat
  | .raise site fold constant => 4 + site.size + foldSize fold constant
  | .make constant => 2 + constantSize constant
  | .message => 2
  | .pick test => 3 + test.size
  | .call _ constant => 3 + constantSize constant

def Decl.size : Decl → Nat
  | .make made => made.size
  | .helper _ word => 4 + operandSize word
  | .message .. => 4
  | .pick _ word first second => 5 + operandSize word + first.size + second.size

def Datum.size : Datum → Nat
  | .pair origin word | .first origin word => 3 + origin.size + operandSize word
  | .inl origin => 2 + origin.size
  | .inr word | .second word => 2 + operandSize word

def Item.size : Item → Nat
  | .action single => actionSize single
  | .site single => single.size

def Step.size : Step → Nat
  | .action single => actionSize single
  | .error decl => 2 + decl.size
  | .data datum => datum.size
  | .site single => 2 + single.size
  | .call _ origin word direct fold constant =>
      20 + origin.size + operandSize word + (if direct then 0 else 2) + foldSize fold constant
  | .take _ inner fold constant => 4 + inner.size + foldSize fold constant
  | .closure inner fold constant => 4 + inner.size + foldSize fold constant
  | .apply _ word fold constant => 3 + operandSize word + foldSize fold constant
  | .loop mask body => 4 + mask + (body.map Item.size).sum

def Plan.size (plan : Plan) : Nat := (plan.helpers.map Helper.size).sum + (plan.steps.map Step.size).sum

/-! Reductions. -/

def removeAt {α : Type} (list : List α) (index : Nat) : List α := list.take index ++ list.drop (index + 1)

/-- Simpler tests: equality with zero, then smaller constants. -/
def Test.reductions : Test → List Test
  | .eq constant => if constant = 0 then [] else [.eq 0]
  | .ne constant | .lt constant | .gt constant => [.eq 0, .eq constant]
  | .bits _ value => [.eq 0, .eq value]

def Operand.reductions (word : Operand) : List Operand :=
  if word == .input then [] else [.input]

def Make.reductions : Make → List Make
  | .empty => []
  | .selector word => [.empty] ++ (Operand.reductions word).map Make.selector
  | .message _ => [.empty]

def Source.reductions : Source → List Source
  | .make made => made.reductions.map Source.make
  | .named _ | .param => [.make .empty]

def Payload.reductions (form : Form) : Payload → List Payload
  | .none => []
  | .literal text => (if text = 0 then [] else [.literal 0]) ++ (if form == .when then [.none] else [])
  | .error origin => origin.reductions.map Payload.error ++ (if form == .when then [.none] else [])
  | .halt kind => if kind.size = 0 then [] else [.halt .inline]

def Site.reductions (site : Site) : List Site :=
  (site.payload.reductions site.form).map (fun payload => {site with payload}) ++
  site.cond.test.reductions.map (fun test => {site with cond := {site.cond with test}}) ++
  (Operand.reductions site.cond.word).map (fun word => {site with cond := {site.cond with word}}) ++
  (if site.form == .require then
    match site.payload with
    | .error _ => [{site with form := .when}]
    | .literal text => [{site with form := .when, payload := .literal (if literalLength text ≤ 32 then text else 0)}]
    | .none | .halt _ => []
  else [])

def foldReductions (fold : Fold) (constant : Nat) : List (Fold × Nat) :=
  (if fold == .xor then [(.add, constant)] else []) ++ (if constant = 3 then [] else [(fold, 3)])

def Helper.reductions : Helper → List Helper
  | .raise site fold constant =>
      site.reductions.map (fun site => .raise site fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .raise site fold constant
  | .make constant => if constant = 1 then [] else [.make 1]
  | .message => []
  | .pick test => test.reductions.map Helper.pick
  | .call callee constant => if constant = 1 then [] else [.call callee 1]

def Decl.reductions : Decl → List Decl
  | .make made => made.reductions.map Decl.make
  | .helper _ _ | .message .. | .pick .. => [.make .empty]

def Datum.reductions : Datum → List Datum
  | .pair origin word => origin.reductions.map (fun origin => .pair origin word) ++
      (Operand.reductions word).map (Datum.pair origin)
  | .inl origin => origin.reductions.map Datum.inl
  | .inr word => (Operand.reductions word).map Datum.inr
  | .first origin word => [Datum.second word] ++ origin.reductions.map (fun origin => .first origin word)
  | .second word => (Operand.reductions word).map Datum.second

/-- The site a call reaches, with its parameter replaced by the call's
argument and its Word by the input, as a site of `run`. -/
def callSite (helpers : List Helper) (helper : Nat) (origin : Source) : Option Site := do
  let (site, _, _, _) ← resolve helpers (maximumHelpers + 1) helper
  let payload := match site.payload with
    | .error .param => .error origin
    | .error (.make (.selector _)) => .error (.make (.selector .input))
    | payload => payload
  return {site with payload, cond := {site.cond with word := .input}}

def Step.reductions (helpers : List Helper) : Step → List Step
  | .action _ => []
  | .error decl => decl.reductions.map Step.error
  | .data datum => datum.reductions.map Step.data
  | .site single => single.reductions.map Step.site
  | .call helper origin word direct fold constant =>
      ((callSite helpers helper origin).map Step.site).toList ++
      (if direct then [] else [.call helper origin word true fold constant]) ++
      origin.reductions.map (fun origin => .call helper origin word direct fold constant) ++
      (Operand.reductions word).map (fun word => .call helper origin word direct fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .call helper origin word direct fold constant
  | .take held inner fold constant =>
      inner.reductions.map (fun reduced => .take held reduced fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .take held inner fold constant
  | .closure inner fold constant =>
      inner.reductions.map (fun reduced => .closure reduced fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .closure inner fold constant
  | .apply number word fold constant =>
      (Operand.reductions word).map (fun word => .apply number word fold constant) ++
      (foldReductions fold constant).map fun (fold, constant) => .apply number word fold constant
  | .loop mask body =>
      (if mask = 1 then [] else [.loop (if mask = 7 then 3 else 1) body]) ++
      ((List.range body.length).filterMap fun index =>
        if body.length > 1 then some (.loop mask (removeAt body index)) else none) ++
      (List.range body.length).flatMap fun index => match (body[index]? : Option Item) with
        | some (Item.site inner) => inner.reductions.map fun reduced => .loop mask (body.set index (Item.site reduced))
        | _ => []

/-- References to helpers after one is removed: later ones move down. -/
def shiftHelper (removed index : Nat) : Nat := if index > removed then index - 1 else index

def Step.usesHelper (helper : Nat) : Step → Bool
  | .error (.helper target _) | .error (.message target _) | .error (.pick target ..) => target == helper
  | .call target .. => target == helper
  | _ => false

def Step.shiftHelpers (removed : Nat) : Step → Step
  | .error (.helper target word) => .error (.helper (shiftHelper removed target) word)
  | .error (.message target value) => .error (.message (shiftHelper removed target) value)
  | .error (.pick target word first second) => .error (.pick (shiftHelper removed target) word first second)
  | .call target origin word direct fold constant => .call (shiftHelper removed target) origin word direct fold constant
  | step => step

def Helper.shift (removed : Nat) : Helper → Helper
  | .call callee constant => .call (shiftHelper removed callee) constant
  | helper => helper

def Helper.calls (helper : Nat) : Helper → Bool
  | .call callee _ => callee == helper
  | _ => false

/-- The plan's reductions: remove a step, remove a helper nothing calls, then
each step's and helper's own. Admission is checked when a reduction is
sealed. -/
def planReductions (plan : Plan) : List Plan :=
  ((List.range plan.steps.length).map fun index => {plan with steps := removeAt plan.steps index}) ++
  ((List.range plan.helpers.length).filterMap fun index =>
    if plan.steps.any (·.usesHelper index) || plan.helpers.any (·.calls index) then none
    else some {helpers := (removeAt plan.helpers index).map (Helper.shift index),
               steps := plan.steps.map (Step.shiftHelpers index)}) ++
  ((List.range plan.steps.length).flatMap fun index =>
    ((plan.steps.getD index default).reductions plan.helpers).map fun step => {plan with steps := plan.steps.set index step}) ++
  ((List.range plan.helpers.length).flatMap fun index =>
    (plan.helpers.getD index default).reductions.map fun helper => {plan with helpers := plan.helpers.set index helper})

end Solcore.Synthesis.Core.RevertData
end

section
-- leanmerge: from Solcore.Synthesis.Source.RevertDataEmitter
/-! The Solcore source of a revert data plan: the helpers `sc_h<k>` that
raise, make, choose and forward std `Error` values, the enum `Sc_F` when a
plan uses it, and `SynthesizedRevertData.run(uint256)`, whose
`runtime-memory-values` actions keep that profile's text. The source is a
function of the plan; nothing here builds or reads the Core reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RevertData

open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Operand)

def emitterVersion : String := "solcore-source-revert-data-v2"
def wrapperVersion : String := "solcore-word-revert-data-contract-v1"
def contractName : String := "SynthesizedRevertData"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def deployPath : List String := ["SynthesizedRevertDataDeploy"]
def runtimePath : List String := ["SynthesizedRevertDataDeploy", "SynthesizedRevertData"]

private def foldText : Fold → String
  | .add => " + "
  | .xor => " ^ "

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def testText (word : String) : Test → String
  | .lt constant => "(" ++ word ++ " < " ++ toString constant ++ ")"
  | .gt constant => "(" ++ word ++ " > " ++ toString constant ++ ")"
  | .eq constant => "(" ++ word ++ " == " ++ toString constant ++ ")"
  | .ne constant => "(" ++ word ++ " != " ++ toString constant ++ ")"
  | .bits mask value => "((" ++ word ++ " & " ++ toString mask ++ ") == " ++ toString value ++ ")"

/-- A Word of `run`, its loop and match arms. -/
def runWord : Operand → String := Source.MemoryValues.operandText "sc_counter"

/-- A Word of a helper or closure over its parameter. -/
def localWord (base : String) : Operand → String
  | .add constant => "(" ++ base ++ " + " ++ toString constant ++ ")"
  | .mul constant => "(" ++ base ++ " * " ++ toString constant ++ ")"
  | .xor constant => "(" ++ base ++ " ^ " ++ toString constant ++ ")"
  | _ => base

def bytesName (value : Nat) : String := "sc_b" ++ toString value

def makeText (word : Operand → String) : Make → String
  | .selector selector => "Error(" ++ word selector ++ ")"
  | .empty => "Error.Empty"
  | .message value => "Error.Msg(memory(Typedef.rep(" ++ bytesName value ++ ")))"

def sourceText (word : Operand → String) : Source → String
  | .make made => makeText word made
  | .named number => "sc_e" ++ toString number
  | .param => "sc_e"

def literalText (text : Nat) : String := "\"" ++ (literals[text]?).getD "" ++ "\""

/-- A Word in Yul: `run`'s, or a helper's or closure's over its parameter. -/
def yulWord (base : String) : Operand → String
  | .add constant => "add(" ++ base ++ ", " ++ toString constant ++ ")"
  | .mul constant => "mul(" ++ base ++ ", " ++ toString constant ++ ")"
  | .xor constant => "xor(" ++ base ++ ", " ++ toString constant ++ ")"
  | .acc => "sc_r"
  | .counter => "sc_counter"
  | .input => base

def yulTest (word : String) : Test → String
  | .lt constant => "lt(" ++ word ++ ", " ++ toString constant ++ ")"
  | .gt constant => "gt(" ++ word ++ ", " ++ toString constant ++ ")"
  | .eq constant => "eq(" ++ word ++ ", " ++ toString constant ++ ")"
  | .ne constant => "iszero(eq(" ++ word ++ ", " ++ toString constant ++ "))"
  | .bits mask value => "eq(and(" ++ word ++ ", " ++ toString mask ++ "), " ++ toString value ++ ")"

/-- A site's lines over the Words of its scope, `yul` naming them in Yul. -/
def siteLines (word : Operand → String) (site : Site) (yul : Operand → String := yulWord "sc_x") : List String :=
  let condition := testText (word site.cond.word) site.cond.test
  let guarded := fun (line : String) => ["if " ++ condition ++ " {", "    " ++ line, "}"]
  match site.form, site.payload with
  | .when, .error origin => guarded ("revertWithError(" ++ sourceText word origin ++ ");")
  | .require, .error origin => ["require(" ++ condition ++ ", " ++ sourceText word origin ++ ");"]
  | .when, .literal text => guarded ("revertLit(" ++ literalText text ++ ");")
  | .require, .literal text => ["require(" ++ condition ++ ", " ++ literalText text ++ ");"]
  | _, .none => guarded "revertEmpty();"
  | _, .halt .assert => ["assert(" ++ condition ++ ");"]
  | _, .halt .opcode => guarded "invalid();"
  | _, .halt .inline => ["if " ++ condition ++ " {", "    assembly {", "        invalid()", "    }", "}"]
  | _, .halt .yul =>
      ["assembly {", "    if " ++ yulTest (yul site.cond.word) site.cond.test ++ " {", "        invalid()", "    }", "}"]

def helperName (index : Nat) : String := "sc_h" ++ toString index

def helperLines (index : Nat) : Helper → List String
  | .raise site fold constant =>
      ["function " ++ helperName index ++ "(sc_e: Error, sc_w: word) returns (word) {"] ++
      indent 4 (siteLines (localWord "sc_w") site (yulWord "sc_w")) ++
      ["    return (sc_w" ++ foldText fold ++ toString constant ++ ");", "}"]
  | .make constant =>
      ["function " ++ helperName index ++ "(sc_w: word) returns (Error) {",
       "    return Error((sc_w + " ++ toString constant ++ "));", "}"]
  | .message =>
      ["function " ++ helperName index ++ "(sc_v: memory<bytes>) returns (Error) {",
       "    return Error.Msg(memory(Typedef.rep(sc_v)));", "}"]
  | .pick test =>
      ["function " ++ helperName index ++ "(sc_w: word, sc_a: Error, sc_b: Error) returns (Error) {",
       "    if " ++ testText "sc_w" test ++ " {", "        return sc_a;", "    }", "    return sc_b;", "}"]
  | .call callee constant =>
      ["function " ++ helperName index ++ "(sc_e: Error, sc_w: word) returns (word) {",
       "    return " ++ helperName callee ++ "(sc_e, (sc_w + " ++ toString constant ++ "));", "}"]

/-- Declaration numbers so far, by kind. -/
structure Names where
  values : Source.MemoryValues.Names := {}
  errors : Nat := 0
  pairs : Nat := 0
  sums : Nat := 0
  enums : Nat := 0
  closures : Nat := 0
  functions : Nat := 0

def foldLine (fold : Fold) (constant : Nat) (value : String) : String :=
  "sc_r = ((sc_r * " ++ toString constant ++ ")" ++ foldText fold ++ value ++ ");"

def declText : Decl → String
  | .make made => makeText runWord made
  | .helper helper word => helperName helper ++ "(" ++ runWord word ++ ")"
  | .message helper value => helperName helper ++ "(" ++ bytesName value ++ ")"
  | .pick helper word first second =>
      helperName helper ++ "(" ++ runWord word ++ ", " ++ sourceText runWord first ++ ", " ++
        sourceText runWord second ++ ")"

def takeLines (held : Held) (site : Site) (fold : Fold) (constant : Nat) : List String :=
  let arm := siteLines runWord site
  let folded := [foldLine fold constant "sc_w"]
  match held with
  | .pair number =>
      ["match (sc_t" ++ toString number ++ ") {", "    case (sc_e, sc_w) {"] ++ indent 8 (arm ++ folded) ++
      ["    }", "}"]
  | .sum number =>
      ["match (sc_u" ++ toString number ++ ") {", "    case inl(sc_e) {"] ++ indent 8 arm ++
      ["    }", "    case inr(sc_w) {"] ++ indent 8 folded ++ ["    }", "}"]
  | .enum number =>
      ["match (sc_g" ++ toString number ++ ") {", "    case Sc_F.Sc_F0(sc_e, sc_w) {"] ++ indent 8 (arm ++ folded) ++
      ["    }", "    case Sc_F.Sc_F1(sc_w) {"] ++ indent 8 folded ++ ["    }", "}"]

/-- A step's lines and the declaration numbers after it. -/
def stepLines (names : Names) : Step → List String × Names
  | .action action =>
      let (lines, values) := Source.MemoryValues.actionLines "sc_counter" names.values action
      (lines, {names with values})
  | .error decl =>
      (["let sc_e" ++ toString names.errors ++ ": Error = " ++ declText decl ++ ";"],
       {names with errors := names.errors + 1})
  | .data datum =>
      let error := fun (origin : Source) => sourceText runWord origin
      match datum with
      | .pair origin word =>
          (["let sc_t" ++ toString names.pairs ++ ": (Error, word) = (" ++ error origin ++ ", " ++ runWord word ++ ");"],
           {names with pairs := names.pairs + 1})
      | .inl origin =>
          (["let sc_u" ++ toString names.sums ++ ": sum<Error, word> = inl(" ++ error origin ++ ");"],
           {names with sums := names.sums + 1})
      | .inr word =>
          (["let sc_u" ++ toString names.sums ++ ": sum<Error, word> = inr(" ++ runWord word ++ ");"],
           {names with sums := names.sums + 1})
      | .first origin word =>
          (["let sc_g" ++ toString names.enums ++ ": Sc_F = Sc_F.Sc_F0(" ++ error origin ++ ", " ++ runWord word ++ ");"],
           {names with enums := names.enums + 1})
      | .second word =>
          (["let sc_g" ++ toString names.enums ++ ": Sc_F = Sc_F.Sc_F1(" ++ runWord word ++ ");"],
           {names with enums := names.enums + 1})
  | .site site => (siteLines runWord site, names)
  | .call helper origin word direct fold constant =>
      let arguments := "(" ++ sourceText runWord origin ++ ", " ++ runWord word ++ ")"
      if direct then ([foldLine fold constant (helperName helper ++ arguments)], names)
      else
        let name := "sc_f" ++ toString names.functions
        (["let " ++ name ++ ": function (Error, word) returns (word) = " ++ helperName helper ++ ";",
          foldLine fold constant (name ++ arguments)], {names with functions := names.functions + 1})
  | .take held site fold constant => (takeLines held site fold constant, names)
  | .closure site fold constant =>
      (["let sc_c" ++ toString names.closures ++ ": function (word) returns (word) = lam (sc_j: word) -> word {"] ++
        indent 4 (siteLines (localWord "sc_j") site (yulWord "sc_j")) ++
        ["    return (sc_j" ++ foldText fold ++ toString constant ++ ");", "};"],
       {names with closures := names.closures + 1})
  | .apply closure word fold constant =>
      ([foldLine fold constant ("sc_c" ++ toString closure ++ "(" ++ runWord word ++ ")")], names)
  | .loop mask body =>
      let (inner, values) := body.foldl (fun (lines, values) item => match item with
        | .action action =>
            let (more, values) := Source.MemoryValues.actionLines "sc_counter" values action
            (lines ++ more, values)
        | .site site => (lines ++ siteLines runWord site, values)) ([], names.values)
      (["let sc_limit: word = (sc_x & " ++ toString mask ++ ");",
        "let sc_counter: word = 0;",
        "while (sc_limit > sc_counter) {"] ++ indent 4 inner ++
       ["    sc_counter = (sc_counter + 1);", "}"], {names with values})

def Step.actions : Step → List Solcore.Synthesis.Core.MemoryValues.Action
  | .action action => [action]
  | .loop _ body => body.filterMap fun item => match item with
      | .action action => some action
      | .site _ => none
  | _ => []

def usesEnum (plan : Plan) : Bool :=
  plan.steps.any fun step => match step with
    | .data (.first ..) | .data (.second _) => true
    | _ => false

/-- The source with its contract and std.opcodes imports. -/
def emitWith (contract : String) (opcodes : String) (plan : Plan) : EmittedProgram := Id.run do
  let mut names : Names := {}
  let mut lines : List String := []
  for step in plan.steps do
    let (more, next) := stepLines names step
    lines := lines ++ more
    names := next
  let used := plan.steps.flatMap fun step => (Step.actions step).flatMap Source.MemoryValues.actionHelpers
  let actionHelpers := Source.MemoryValues.helperNames.filter used.contains
  let enum := if usesEnum plan then ["enum Sc_F {", "    Sc_F0(Error, word),", "    Sc_F1(word)", "}", ""] else []
  let helpers := plan.helpers.zipIdx.flatMap fun (helper, index) => helperLines index helper ++ [""]
  let source := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    opcodes, ""] ++
    actionHelpers.flatMap Source.MemoryValues.helperLines ++ enum ++ helpers ++
    ["contract " ++ contract ++ " {",
     "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
     "        let sc_x: word = Typedef.rep(input);",
     "        let sc_r: word = 0;"] ++ indent 8 lines ++
    ["        return uint256(sc_r);", "    }", "}"]
  return {
    source := String.intercalate "\n" source ++ "\n"
    contractName := contract, methodName, methodSignature, deployPath := [contract ++ "Deploy"],
    runtimePath := [contract ++ "Deploy", contract]
  }

def emit (plan : Plan) : EmittedProgram :=
  emitWith contractName "import { mload, mstore, mstore8, shr, mod } from std.opcodes;" plan

end Solcore.Synthesis.Source.RevertData
end

section
-- leanmerge: from Solcore.Synthesis.Source.RevertDataCases
/-! A revert data case retains its plan, drawn from the case seed, and the
plan's complete original Core reference at the case input. The reference is
`runtime-memory-values`' byte-list model with every helper and closure
inlined, built from the plan, never from the source. Its right injection is
the revert data: a length and two Words, observed as the bytes they hold.
Saved observations never supply the oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RevertData
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Ref Fold Width Operand Index)

def caseSchema : String := "solcore-lean.semantic-revert-data-case.v1"
def planSchema : String := "solcore-lean.revert-data-plan.v1"
def profileVersion : String := "runtime-revert-data-v1/plan-seed-v1"

/-- The node budget, which bounds the applied reference, and the decode bound
of a saved reference. -/
def defaultNodes : Nat := 1024
def minimumNodes : Nat := 256
def maximumNodes : Nat := 2048
def caseLimit : Nat := 4096

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

/-! Plan JSON, with `runtime-memory-values`' encoding of operands and
actions. Every decoder is strict and the decoded plan must re-encode to the
saved JSON. -/

private def foldName : Fold → String
  | .add => "add"
  | .xor => "xor"

private def foldOf (text : String) : Except String Fold :=
  match text with
  | "add" => .ok .add
  | "xor" => .ok .xor
  | _ => .error "unknown revert data fold"

def testJson : Test → Json
  | .lt constant => Json.mkObj [("test", toJson "lt"), ("constant", toJson constant)]
  | .gt constant => Json.mkObj [("test", toJson "gt"), ("constant", toJson constant)]
  | .eq constant => Json.mkObj [("test", toJson "eq"), ("constant", toJson constant)]
  | .ne constant => Json.mkObj [("test", toJson "ne"), ("constant", toJson constant)]
  | .bits mask value => Json.mkObj [("test", toJson "bits"), ("mask", toJson mask), ("value", toJson value)]

def condJson (cond : Cond) : Json :=
  Json.mkObj [("word", MemoryValues.operandJson cond.word), ("test", testJson cond.test)]

def makeJson : Make → Json
  | .selector word => Json.mkObj [("make", toJson "selector"), ("word", MemoryValues.operandJson word)]
  | .empty => Json.mkObj [("make", toJson "empty")]
  | .message value => Json.mkObj [("make", toJson "message"), ("value", toJson value)]

def sourceJson : Source → Json
  | .make made => Json.mkObj [("source", toJson "make"), ("make", makeJson made)]
  | .named number => Json.mkObj [("source", toJson "named"), ("number", toJson number)]
  | .param => Json.mkObj [("source", toJson "param")]

def payloadJson : Payload → Json
  | .error origin => Json.mkObj [("payload", toJson "error"), ("source", sourceJson origin)]
  | .literal text => Json.mkObj [("payload", toJson "literal"), ("text", toJson text)]
  | .none => Json.mkObj [("payload", toJson "none")]
  | .halt halt => Json.mkObj [("payload", toJson "halt"), ("halt", toJson halt.name)]

def siteJson (site : Site) : Json := Json.mkObj [
  ("form", toJson (match site.form with
    | .when => "when"
    | .require => "require")), ("cond", condJson site.cond), ("payload", payloadJson site.payload)]

def helperJson : Helper → Json
  | .raise site fold constant => Json.mkObj [("kind", toJson "raise"), ("site", siteJson site),
      ("fold", toJson (foldName fold)), ("constant", toJson constant)]
  | .make constant => Json.mkObj [("kind", toJson "make"), ("constant", toJson constant)]
  | .message => Json.mkObj [("kind", toJson "message")]
  | .pick test => Json.mkObj [("kind", toJson "pick"), ("test", testJson test)]
  | .call callee constant => Json.mkObj [("kind", toJson "call"), ("callee", toJson callee), ("constant", toJson constant)]

def declJson : Decl → Json
  | .make made => Json.mkObj [("decl", toJson "make"), ("make", makeJson made)]
  | .helper helper word => Json.mkObj [("decl", toJson "helper"), ("helper", toJson helper),
      ("word", MemoryValues.operandJson word)]
  | .message helper value => Json.mkObj [("decl", toJson "message"), ("helper", toJson helper), ("value", toJson value)]
  | .pick helper word first second => Json.mkObj [("decl", toJson "pick"), ("helper", toJson helper),
      ("word", MemoryValues.operandJson word), ("first", sourceJson first), ("second", sourceJson second)]

def datumJson : Datum → Json
  | .pair origin word => Json.mkObj [("datum", toJson "pair"), ("error", sourceJson origin),
      ("word", MemoryValues.operandJson word)]
  | .inl origin => Json.mkObj [("datum", toJson "inl"), ("error", sourceJson origin)]
  | .inr word => Json.mkObj [("datum", toJson "inr"), ("word", MemoryValues.operandJson word)]
  | .first origin word => Json.mkObj [("datum", toJson "enum0"), ("error", sourceJson origin),
      ("word", MemoryValues.operandJson word)]
  | .second word => Json.mkObj [("datum", toJson "enum1"), ("word", MemoryValues.operandJson word)]

def heldJson : Held → Json
  | .pair number => Json.mkObj [("held", toJson "pair"), ("number", toJson number)]
  | .sum number => Json.mkObj [("held", toJson "sum"), ("number", toJson number)]
  | .enum number => Json.mkObj [("held", toJson "enum"), ("number", toJson number)]

def itemJson : Item → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .site single => Json.mkObj [("site", siteJson single)]

def stepJson : Step → Json
  | .action single => Json.mkObj [("action", MemoryValues.actionJson single)]
  | .error decl => Json.mkObj [("error", declJson decl)]
  | .data datum => Json.mkObj [("data", datumJson datum)]
  | .site single => Json.mkObj [("site", siteJson single)]
  | .call helper origin word direct fold constant => Json.mkObj [("call", Json.mkObj [
      ("helper", toJson helper), ("error", sourceJson origin), ("word", MemoryValues.operandJson word),
      ("form", toJson (if direct then "direct" else "value")), ("fold", toJson (foldName fold)),
      ("constant", toJson constant)])]
  | .take held inner fold constant => Json.mkObj [("take", Json.mkObj [("held", heldJson held),
      ("site", siteJson inner), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .closure inner fold constant => Json.mkObj [("closure", Json.mkObj [("site", siteJson inner),
      ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .apply number word fold constant => Json.mkObj [("apply", Json.mkObj [("closure", toJson number),
      ("word", MemoryValues.operandJson word), ("fold", toJson (foldName fold)), ("constant", toJson constant)])]
  | .loop mask body => Json.mkObj [("loop", Json.mkObj [("mask", toJson mask),
      ("body", .arr (body.map itemJson).toArray)])]

def planJsonWith (schema : String) (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson schema), ("helpers", .arr (plan.helpers.map helperJson).toArray),
  ("steps", .arr (plan.steps.map stepJson).toArray)]

def planJson (plan : Plan) : Json := planJsonWith planSchema plan

private def array (json : Json) (key : String) : Except String (List Json) := do
  return (← json.getObjValAs? (Array Json) key).toList

def testOf (json : Json) : Except String Test := do
  match ← json.getObjValAs? String "test" with
  | "lt" => return .lt (← json.getObjValAs? Nat "constant")
  | "gt" => return .gt (← json.getObjValAs? Nat "constant")
  | "eq" => return .eq (← json.getObjValAs? Nat "constant")
  | "ne" => return .ne (← json.getObjValAs? Nat "constant")
  | "bits" => return .bits (← json.getObjValAs? Nat "mask") (← json.getObjValAs? Nat "value")
  | _ => throw "unknown revert data test"

def condOf (json : Json) : Except String Cond := do
  return {word := ← MemoryValues.operandOf (← json.getObjVal? "word"), test := ← testOf (← json.getObjVal? "test")}

def makeOf (json : Json) : Except String Make := do
  match ← json.getObjValAs? String "make" with
  | "selector" => return .selector (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "empty" => return .empty
  | "message" => return .message (← json.getObjValAs? Nat "value")
  | _ => throw "unknown revert data make"

def sourceOf (json : Json) : Except String Source := do
  match ← json.getObjValAs? String "source" with
  | "make" => return .make (← makeOf (← json.getObjVal? "make"))
  | "named" => return .named (← json.getObjValAs? Nat "number")
  | "param" => return .param
  | _ => throw "unknown revert data source"

def haltOf (text : String) : Except String Halt :=
  match [Halt.assert, .opcode, .inline, .yul].find? (·.name == text) with
  | some halt => .ok halt
  | none => .error "unknown halt"

def payloadOf (json : Json) : Except String Payload := do
  match ← json.getObjValAs? String "payload" with
  | "error" => return .error (← sourceOf (← json.getObjVal? "source"))
  | "literal" => return .literal (← json.getObjValAs? Nat "text")
  | "none" => return .none
  | "halt" => return .halt (← haltOf (← json.getObjValAs? String "halt"))
  | _ => throw "unknown revert data payload"

def siteOf (json : Json) : Except String Site := do
  let form ← match ← json.getObjValAs? String "form" with
    | "when" => pure Form.when
    | "require" => pure Form.require
    | _ => throw "unknown revert data form"
  return {form, cond := ← condOf (← json.getObjVal? "cond"), payload := ← payloadOf (← json.getObjVal? "payload")}

def helperOf (json : Json) : Except String Helper := do
  match ← json.getObjValAs? String "kind" with
  | "raise" =>
      let site ← siteOf (← json.getObjVal? "site")
      let fold ← foldOf (← json.getObjValAs? String "fold")
      return .raise site fold (← json.getObjValAs? Nat "constant")
  | "make" => return .make (← json.getObjValAs? Nat "constant")
  | "message" => return .message
  | "pick" => return .pick (← testOf (← json.getObjVal? "test"))
  | "call" => return .call (← json.getObjValAs? Nat "callee") (← json.getObjValAs? Nat "constant")
  | _ => throw "unknown revert data helper"

def declOf (json : Json) : Except String Decl := do
  match ← json.getObjValAs? String "decl" with
  | "make" => return .make (← makeOf (← json.getObjVal? "make"))
  | "helper" => return .helper (← json.getObjValAs? Nat "helper") (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "message" => return .message (← json.getObjValAs? Nat "helper") (← json.getObjValAs? Nat "value")
  | "pick" =>
      let helper ← json.getObjValAs? Nat "helper"
      let word ← MemoryValues.operandOf (← json.getObjVal? "word")
      let first ← sourceOf (← json.getObjVal? "first")
      return .pick helper word first (← sourceOf (← json.getObjVal? "second"))
  | _ => throw "unknown revert data declaration"

def datumOf (json : Json) : Except String Datum := do
  match ← json.getObjValAs? String "datum" with
  | "pair" => return .pair (← sourceOf (← json.getObjVal? "error")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "inl" => return .inl (← sourceOf (← json.getObjVal? "error"))
  | "inr" => return .inr (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum0" => return .first (← sourceOf (← json.getObjVal? "error")) (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | "enum1" => return .second (← MemoryValues.operandOf (← json.getObjVal? "word"))
  | _ => throw "unknown revert data datum"

def heldOf (json : Json) : Except String Held := do
  let number ← json.getObjValAs? Nat "number"
  match ← json.getObjValAs? String "held" with
  | "pair" => return .pair number
  | "sum" => return .sum number
  | "enum" => return .enum number
  | _ => throw "unknown revert data data variable"

def itemOf (json : Json) : Except String Item := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  return .site (← siteOf (← json.getObjVal? "site"))

def stepOf (json : Json) : Except String Step := do
  if let .ok single := json.getObjVal? "action" then return .action (← MemoryValues.actionOf single)
  if let .ok decl := json.getObjVal? "error" then return .error (← declOf decl)
  if let .ok datum := json.getObjVal? "data" then return .data (← datumOf datum)
  if let .ok single := json.getObjVal? "site" then return .site (← siteOf single)
  if let .ok call := json.getObjVal? "call" then
    let direct ← match ← call.getObjValAs? String "form" with
      | "direct" => pure true
      | "value" => pure false
      | _ => throw "unknown revert data call form"
    let helper ← call.getObjValAs? Nat "helper"
    let origin ← sourceOf (← call.getObjVal? "error")
    let word ← MemoryValues.operandOf (← call.getObjVal? "word")
    let fold ← foldOf (← call.getObjValAs? String "fold")
    return .call helper origin word direct fold (← call.getObjValAs? Nat "constant")
  if let .ok take := json.getObjVal? "take" then
    let held ← heldOf (← take.getObjVal? "held")
    let site ← siteOf (← take.getObjVal? "site")
    let fold ← foldOf (← take.getObjValAs? String "fold")
    return .take held site fold (← take.getObjValAs? Nat "constant")
  if let .ok closure := json.getObjVal? "closure" then
    let site ← siteOf (← closure.getObjVal? "site")
    let fold ← foldOf (← closure.getObjValAs? String "fold")
    return .closure site fold (← closure.getObjValAs? Nat "constant")
  if let .ok applied := json.getObjVal? "apply" then
    let number ← applied.getObjValAs? Nat "closure"
    let word ← MemoryValues.operandOf (← applied.getObjVal? "word")
    let fold ← foldOf (← applied.getObjValAs? String "fold")
    return .apply number word fold (← applied.getObjValAs? Nat "constant")
  let loop ← json.getObjVal? "loop"
  return .loop (← loop.getObjValAs? Nat "mask") (← (← array loop "body").mapM itemOf)

def planOfWith (schema : String) (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = schema do throw "unsupported revert data plan schema"
  return {helpers := ← (← array json "helpers").mapM helperOf, steps := ← (← array json "steps").mapM stepOf}

def planOf (json : Json) : Except String Plan := planOfWith planSchema json

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOf json
  unless plan.admitted do
    throw "revert data plan is outside the admitted helpers, steps, sites, values and literals"
  let some checked := CheckedPlan.ofPlan? plan | throw "revert data reference failed the full Core checker"
  unless json == planJson plan do throw "saved revert data plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "revert data reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.shapes.map fun (dimension, values) => (dimension, toJson values))

/-! Observation: the reference's right injection is the revert data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

def wordBytes (value : Nat) : List Nat := (List.range 32).reverse.map fun index => (value / 256 ^ index) % 256

/-- A returned Word, or revert data. -/
inductive Outcome where
  | word (value : Word)
  | reverted (data : List Nat)
  deriving BEq

def Outcome.ofValue? : Value → Option Outcome
  | .inLeft _ (.word returned) => some (.word returned)
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("revertDataPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson revertVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("revertDataShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "revert data reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic revert data case schema"
  let plan ← checkedPlan (← json.getObjVal? "revertDataPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its revert data plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some outcome => .ok outcome
        | none => .error "boundary observation did not return a Word or revert data"
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
    | .reverted _ => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generate seed.toUInt64).fit nodes
  unless plan.nodes ≤ nodes do throw "revert data reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "revert data reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "revert-data-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
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
          throw "revert data node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel acceptance
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "revert-data-profile"), ("reason", toJson error),
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
      ("profileVersion", profileVersion), ("generatorVersion", revertVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the revert data plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the revert data wrapper"
  unless (← provenance.getObjVal? "revertDataShapes") == shapesJson admitted.plan.plan do
    throw "saved revert data shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "revert-data-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported revert data case origin"
  if kind = "revert-data-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved revert data plan differs from its generation seed"
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
      throw "generated revert data provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported revert data provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved revert data reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced revert data provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "revert data provenance contains unexpected fields"
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

end Solcore.Synthesis.Source.RevertData
end

section
-- leanmerge: from Solcore.Synthesis.Source.HaltCases
/-! A `runtime-halts` case retains its plan, a `runtime-revert-data` plan whose
sites can also halt with INVALID, drawn from the case seed, and the plan's
complete original Core reference at the case input. The reference is
`runtime-revert-data`'s, built from the plan, never from the source: a halt
site raises the right injection with a length no revert data has, `2^256 − 1`,
and no bytes, observed as INVALID's halt. Saved observations never supply the
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Halts
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Source.RevertData (planJsonWith planOfWith hexBytes wordBytes)

def caseSchema : String := "solcore-lean.semantic-halt-case.v1"
def planSchema : String := "solcore-lean.halt-plan.v1"
def profileVersion : String := "runtime-halts-v1/plan-seed-v1"
def haltVersion : String := "core-halt-v1"
def emitterVersion : String := "solcore-source-halt-v2"
def wrapperVersion : String := "solcore-word-halt-contract-v1"
def contractName : String := "SynthesizedHalts"

/-- The node budget, which bounds the applied reference, and the decode bound
of a saved reference: `runtime-revert-data`'s. -/
def defaultNodes : Nat := RevertData.defaultNodes
def minimumNodes : Nat := RevertData.minimumNodes
def maximumNodes : Nat := RevertData.maximumNodes
def caseLimit : Nat := RevertData.caseLimit

/-- An admitted halt plan whose reference passes the full Core checker. The
input is a literal, so the check at zero holds at every input. -/
structure CheckedPlan where private mk ::
  plan : Plan
  admitted : plan.haltAdmitted = true
  checked : (plan.applied Word.zero).check = true

namespace CheckedPlan

def ofPlan? (plan : Plan) : Option CheckedPlan :=
  if admitted : plan.haltAdmitted = true then
    if checked : (plan.applied Word.zero).check = true then some ⟨plan, admitted, checked⟩ else none
  else none

def program (plan : CheckedPlan) (input : Word) : Wire.Program := plan.plan.applied input

end CheckedPlan

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program := value.plan.program value.input

def planJson (plan : Plan) : Json := planJsonWith planSchema plan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  let plan ← planOfWith planSchema json
  unless plan.haltAdmitted do
    throw "halt plan is outside the admitted helpers, steps, sites, values and literals, or reaches no halt"
  let some checked := CheckedPlan.ofPlan? plan | throw "halt reference failed the full Core checker"
  unless json == planJson plan do throw "saved halt plan differs from its canonical checked representation"
  unless plan.nodes ≤ caseLimit do throw "halt reference exceeds the 4,096-node case limit"
  return checked

def shapesJson (plan : Plan) : Json :=
  Json.mkObj (plan.haltShapes.map fun (dimension, values) => (dimension, toJson values))

def emit (plan : Plan) : EmittedProgram :=
  RevertData.emitWith contractName "import { mload, mstore, mstore8, shr, mod, invalid } from std.opcodes;" plan

/-! Observation: the reference's right injection is revert data, or INVALID's
halt. -/

/-- A returned Word, revert data, or INVALID's halt. -/
inductive Outcome where
  | word (value : Word)
  | reverted (data : List Nat)
  | halted
  deriving BEq

def Outcome.ofValue? : Value → Option Outcome
  | .inLeft _ (.word returned) => some (.word returned)
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val))
      else if length.val = haltLength && first.val = 0 && second.val = 0 then some .halted
      else none
  | _ => none

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | some .halted => [("status", toJson "invalid")]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram) (origin : Json) (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("haltPlan", planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("generatorVersion", toJson haltVersion), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      ("haltShapes", shapesJson plan.plan)]),
    ("contract", Enums.contractJson emitted input), ("executionFuel", toJson fuel),
    ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless plan.plan.nodes ≤ caseLimit do throw "halt reference exceeds the 4,096-node case limit"
  return makeCase plan input (emit plan.plan) origin fuel

/-- Every origin keeps the canonical reference of its plan at its input. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic halt case schema"
  let plan ← checkedPlan (← json.getObjVal? "haltPlan")
  let input ← Primitive.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := caseLimit, maxNodes := caseLimit, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.program input) do
    throw "saved Core program differs from its halt plan's reference and runtime input"
  return ⟨plan, input⟩

/-- A generation filter on the reference, not a claim that this finite bank
covers a plan. -/
def boundaryOutcomes (plan : CheckedPlan) (fuel : Nat) : Except String (List Outcome) := do
  Primitive.boundaryInputs.mapM fun input =>
    match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Outcome.ofValue? value with
        | some outcome => .ok outcome
        | none => .error "boundary observation did not return a Word, revert data or a halt"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "boundary observation produced a Core fault"

/-- At least one boundary input halts, and at least two outcomes differ. A
plan that halts can return none of its inputs, so no identity filter
applies. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  let outcomes ← boundaryOutcomes plan fuel
  unless outcomes.contains .halted do throw "no boundary input halted"
  unless outcomes.any (fun outcome => outcomes.any (fun other => outcome != other)) do
    throw "all eight boundary inputs had the same outcome"

/-- The seed's plan, its steps dropped from the end while the reference
exceeds the budget. -/
def generatedPlan (seed : Seed) (nodes : Nat) : Except String CheckedPlan := do
  let plan := (generateHalts seed.toUInt64).fit nodes (halts := true)
  unless plan.nodes ≤ nodes do throw "halt reference exceeds the node budget"
  let some checked := CheckedPlan.ofPlan? plan
    | throw "halt reference failed admission or the full Core checker"
  return checked

private def generatedOrigin (seed : Seed) (nodes inputIndex fuel : Nat) : Json := Json.mkObj [
  ("kind", toJson "halt-generated"), ("seed", toJson (toString seed.toNat)), ("maxProgramNodes", toJson nodes),
  ("inputIndex", toJson inputIndex), ("validationFuel", toJson fuel)]

/-- Attempt limits count plans; case limits count individual runtime inputs. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
          throw "halt node budget is outside 256 to 2,048"
        let plan ← generatedPlan seed nodes
        inputSensitive plan fuel
        return plan
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "halt-profile"), ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok plan =>
          let emitted := emit plan.plan
          for (input, inputIndex) in (inputSelection.inputs Primitive.boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := inputSelection.record (generatedOrigin seed nodes inputIndex fuel)
              cases := cases.push (makeCase plan input emitted origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-! Reduction: `runtime-revert-data`'s, admitted as halt plans. -/

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
      ("profileVersion", profileVersion), ("generatorVersion", haltVersion),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the halt plan"
  unless (← json.getObjVal? "contract") == Enums.contractJson emitted admitted.input do
    throw "saved contract metadata differs from the halt wrapper"
  unless (← provenance.getObjVal? "haltShapes") == shapesJson admitted.plan.plan do
    throw "saved halt shapes differ from the plan"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "halt-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported halt case origin"
  if kind = "halt-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless minimumNodes ≤ nodes && nodes ≤ maximumNodes do
      throw "saved generation budget exceeds profile limits"
    let plan ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan.plan == planJson admitted.plan.plan do
      throw "saved halt plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs Primitive.boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
    unless origin == inputSelection.record (generatedOrigin (Seed.ofNat seed) nodes inputIndex validationFuel) do
      throw "generated halt provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported halt provenance is not canonical"
  else
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← Primitive.inputWord parentText⟩
    unless decide (admitted.measure.StrictlySmaller parent.measure) do
      throw "saved halt reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced halt provenance is not canonical"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "halt provenance contains unexpected fields"
  return fresh

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
    if bytes + size > RevertData.shrinkBytes then break
    bytes := bytes + size
    cases := cases.push case
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Halts
end
