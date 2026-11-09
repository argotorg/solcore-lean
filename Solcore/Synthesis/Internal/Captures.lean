import Solcore.Synthesis.Internal.Integers

/-!
# Profiles: closure captures and closure factories

The profiles `runtime-closure-captures` and `runtime-closure-factories`.
-/

section
/-! Closures over Words that capture by value, as solcore-rs #120 decided: a
closure keeps the values its captured locals had when it was created, a write in
its body changes only the call's copy, and each call starts again from the
creation-time values. A plan is the body of `run`: Word locals, closures made from
lambdas, aliases and factories, writes through captures, repeated calls, directly
or through the generic `sc_apply` and `sc_twice`, a loop, and a contract field
that bodies and factory methods write and read at call time. A factory returns a
closure over its parameter and locals.

Every local is assigned where it is declared, so no program reads a local before
assigning it, directly or through a capture. Every closure is statically one
lambda, as the pin lowers closures: none is chosen by a branch or rebound in a
loop; none that captures a closure is passed as an argument, captured by a
lambda or made by a rebinding in a body; no factory's result captures a closure;
and a factory that returns one of its own closures has no effect of its own and
is called with arguments that have none. The pin rejects each of these forms with
`SC0422`.

The reference is original Core over Wire cells. A local is a cell. Creating a
closure loads each captured cell into an immutable snapshot, and the lambda
copies every snapshot into a fresh cell at each call, so writes in a body reach
only that call. The field and the fold are cells that every scope shares. A
factory runs where it is called. The right injection is the revert data
`Panic(0x11)` or `Panic(0x12)` of a checked `uint256` operation, which a call
passes on. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Captures

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Enums (Gen draw drawWeighted)
open Solcore.Synthesis.Core.Integers (Env IntType payloadType panicPayload)

def version : String := "core-closure-captures-v1"

/-- A wrapping Word operation. -/
inductive Op where
  | add | sub | mul | xor
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A checked `uint256` operation: `+` panics with `0x11` past `2^256 - 1`,
`/` with `0x12` on a zero divisor. -/
inductive Checked where
  | add | div
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A local of the scope `up` levels out: 0 is the current scope. -/
structure Ref where
  up : Nat
  index : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A Word: a scope's parameter (`sc_x` in `run`, `sc_p` in a factory, `sc_a`
and `sc_b` in lambdas), a Word local of a scope, or the contract field `sc_n`. -/
inductive Var where
  | param (up : Nat)
  | value (ref : Ref)
  | field
  deriving Repr, BEq, DecidableEq, Inhabited

/-- How a term calls a closure: directly, through `sc_apply`, or twice through
`sc_twice`. -/
inductive Via where
  | direct | apply | twice
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Term where
  | lit (value : Nat)
  | var (var : Var)
  | op (op : Op) (left right : Term)
  | checked (op : Checked) (left right : Term)
  | call (via : Via) (closure : Ref) (argument : Term)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A statement of `run`, of a factory or of a lambda body. `observe` and
`loop` are `run`'s alone, and a loop body only assigns and observes. -/
inductive Stmt where
  /-- `let <value>: word = init;` -/
  | value (init : Term)
  /-- `<target> = value;` -/
  | assign (target : Var) (value : Term)
  /-- `let <closure>: F = lam (<param>: word) -> word { body; return result; };` -/
  | lambda (body : List Stmt) (result : Term)
  /-- `let <closure>: F = <source>;` -/
  | alias (source : Ref)
  /-- `let <closure>: F = sc_mk<factory>(argument);` -/
  | make (factory : Nat) (argument : Term)
  /-- `sc_mk<factory>(argument);` -/
  | discard (factory : Nat) (argument : Term)
  /-- `<target> = lam (<param>: word) -> word { body; return result; };` -/
  | relambda (target : Ref) (body : List Stmt) (result : Term)
  /-- `<target> = <source>;` -/
  | realias (target source : Ref)
  /-- `<target> = sc_mk<factory>(argument);` -/
  | remake (target : Ref) (factory : Nat) (argument : Term)
  /-- `sc_r = ((sc_r * 1099511628211) ^ value);` -/
  | observe (value : Term)
  /-- `while (sc_i<k> < count) { body; sc_i<k> = sc_i<k> + 1; }` -/
  | loop (count : Nat) (body : List Stmt)
  deriving Repr, BEq, Inhabited

/-- What a factory returns: one of its closures, or a lambda. -/
inductive Returns where
  | closure (index : Nat)
  | lambda (body : List Stmt) (result : Term)
  deriving Repr, BEq, Inhabited

/-- `sc_mk<k>(sc_p: word)`: a contract method when `method`, which may name the
field and call method factories, otherwise a free function. -/
structure Factory where
  method : Bool
  body : List Stmt
  returns : Returns
  deriving Repr, BEq, Inhabited

structure Plan where
  factories : List Factory
  steps : List Stmt
  deriving Repr, BEq, Inhabited

/-! Bounds. -/

def maximumSteps : Nat := 10
def maximumFactories : Nat := 2
def maximumFactorySteps : Nat := 3
def maximumBody : Nat := 3
def maximumDepth : Nat := 2
def maximumValues : Nat := 4
def maximumClosures : Nat := 4
def maximumLoop : Nat := 3
def maximumLoopBody : Nat := 2
def literals : List Nat := [0, 1, 2, 3, 5, 7, 255]
def foldPrime : Nat := 1099511628211
def modulus : Nat := 2 ^ 256

/-! Static scope. A plan is admitted when every reference names a declared local
of a visible scope, the field is named only where a contract method runs, a
factory calls only earlier factories, and no closure that captures a closure is
passed as an argument. -/

/-- A scope while a plan is checked: whether it is `run`, a factory (and
whether a method) or a lambda, its Word locals so far, and for each closure
whether it captures a closure. -/
inductive Kind where
  | run
  | factory (method : Bool)
  | lambda
  deriving Repr, BEq, DecidableEq, Inhabited

structure Scope where
  kind : Kind
  values : Nat := 0
  closures : List Bool := []
  deriving Repr, Inhabited

/-- What a term `level` scopes inside a lambda's body names outside the lambda,
by scope relative to the scope that creates the lambda. -/
inductive Cap where
  | param (up : Nat)
  | value (up index : Nat)
  | closure (up index : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Cap.isClosure : Cap → Bool
  | .closure .. => true
  | _ => false

def Var.caps (level : Nat) : Var → List Cap
  | .param up => if level < up then [.param (up - level - 1)] else []
  | .value ref => if level < ref.up then [.value (ref.up - level - 1) ref.index] else []
  | .field => []

def Ref.caps (level : Nat) (ref : Ref) : List Cap :=
  if level < ref.up then [.closure (ref.up - level - 1) ref.index] else []

def Term.caps (level : Nat) : Term → List Cap
  | .lit _ => []
  | .var named => named.caps level
  | .op _ left right | .checked _ left right => left.caps level ++ right.caps level
  | .call _ ref argument => ref.caps level ++ argument.caps level

mutual
def Stmt.caps (level : Nat) : Stmt → List Cap
  | .value init => init.caps level
  | .assign target assigned => target.caps level ++ assigned.caps level
  | .lambda body result => Stmt.listCaps (level + 1) body ++ result.caps (level + 1)
  | .alias source => source.caps level
  | .make _ argument | .discard _ argument => argument.caps level
  | .relambda target body result =>
      target.caps level ++ Stmt.listCaps (level + 1) body ++ result.caps (level + 1)
  | .realias target source => target.caps level ++ source.caps level
  | .remake target _ argument => target.caps level ++ argument.caps level
  | .observe observed => observed.caps level
  | .loop _ body => Stmt.listCaps level body

def Stmt.listCaps (level : Nat) : List Stmt → List Cap
  | [] => []
  | stmt :: rest => stmt.caps level ++ Stmt.listCaps level rest
end

/-- What a lambda captures from the scope that creates it and those enclosing
that scope, each once, in order of first mention. -/
def lambdaCaps (body : List Stmt) (result : Term) : List Cap :=
  (Stmt.listCaps 0 body ++ result.caps 0).eraseDups

/-- A lambda captures a closure. -/
def lambdaHolds (body : List Stmt) (result : Term) : Bool := (lambdaCaps body result).any (·.isClosure)

/-- The terms a statement evaluates in its own scope, not in a lambda. -/
def Stmt.ownTerms : Stmt → List Term
  | .value init => [init]
  | .assign _ assigned => [assigned]
  | .make _ argument | .discard _ argument | .remake _ _ argument => [argument]
  | .observe observed => [observed]
  | _ => []

/-- A term names the field, runs a checked operation or calls a closure. -/
def Term.effectful : Term → Bool
  | .lit _ => false
  | .var named => named == .field
  | .op _ left right => left.effectful || right.effectful
  | .checked .. | .call .. => true

private def need (condition : Bool) : Option Unit := if condition then some () else none

namespace Scope

def ofFactory (factory : Factory) : Scope := {kind := .factory factory.method}

def pushValue (scope : Scope) : Scope := {scope with values := scope.values + 1}

def pushClosure (scope : Scope) (holds : Bool) : Scope := {scope with closures := scope.closures ++ [holds]}

end Scope

/-- The checking context: each factory's method flag and whether it returns one
of its own closures, and the factory being checked, if any. -/
structure Static where
  factories : List (Bool × Bool)
  within : Option Nat := none

namespace Static

/-- The outermost scope is `run` or a method factory. -/
def fieldVisible (stack : List Scope) : Bool :=
  match stack.getLast? with
  | some {kind := .run, ..} | some {kind := .factory true, ..} => true
  | _ => false

def factoryAdmitted (static : Static) (stack : List Scope) (index : Nat) : Bool :=
  match static.factories[index]? with
  | none => false
  | some (method, _) =>
      (match static.within with | some current => index < current | none => true) &&
        (!method || fieldVisible stack)

/-- The factory returns one of its own closures; a call of it passes an argument
without effects, the form the pin lowers. -/
def returnsLocal (static : Static) (index : Nat) : Bool := ((static.factories[index]?).map (·.2)).getD false

def callAdmitted (static : Static) (stack : List Scope) (index : Nat) (argument : Term) : Bool :=
  static.factoryAdmitted stack index && !(static.returnsLocal index && argument.effectful)

end Static

def Var.admitted (stack : List Scope) : Var → Bool
  | .param up => up < stack.length
  | .value ref => match stack[ref.up]? with
      | some scope => ref.index < scope.values
      | none => false
  | .field => Static.fieldVisible stack

def Ref.admitted (stack : List Scope) (ref : Ref) : Bool :=
  match stack[ref.up]? with
  | some scope => ref.index < scope.closures.length
  | none => false

def Ref.holds (stack : List Scope) (ref : Ref) : Bool :=
  match stack[ref.up]? with
  | some scope => scope.closures.getD ref.index false
  | none => false

def Term.admitted (stack : List Scope) : Term → Bool
  | .lit literal => literal < modulus
  | .var named => named.admitted stack
  | .op _ left right | .checked _ left right => left.admitted stack && right.admitted stack
  | .call via ref argument =>
      ref.admitted stack && (via == .direct || !ref.holds stack) && argument.admitted stack

/-- Replace the head scope. -/
private def setHead (stack : List Scope) (scope : Scope) : List Scope :=
  match stack with
  | [] => []
  | _ :: rest => scope :: rest

private def setHolds (stack : List Scope) (ref : Ref) (holds : Bool) : List Scope :=
  stack.modify ref.up fun scope => {scope with closures := scope.closures.set ref.index holds}

/-- The head scope is a lambda body. A closure rebound there never comes to
capture a closure, a form the pin rejects with `SC0422`. -/
def inBody (stack : List Scope) : Bool := (stack.head?.map (·.kind == .lambda)).getD false

/-- A loop body assigns and observes; it declares nothing and makes no closure. -/
def Stmt.loopStatement : Stmt → Bool
  | .assign .. | .observe _ => true
  | _ => false

mutual
/-- Check one statement and give the scopes after it. -/
def Stmt.check? (static : Static) (stack : List Scope) : Stmt → Option (List Scope)
  | .value init => do
      need (init.admitted stack)
      let head ← stack.head?
      need (head.values < maximumValues)
      return setHead stack head.pushValue
  | .assign target assigned => do
      need (target.admitted stack && assigned.admitted stack)
      return stack
  | .lambda body result => do
      let holds ← Stmt.lambdaCheck? static stack body result
      let head ← stack.head?
      need (head.closures.length < maximumClosures)
      return setHead stack (head.pushClosure holds)
  | .alias source => do
      need (source.admitted stack)
      let head ← stack.head?
      need (head.closures.length < maximumClosures)
      return setHead stack (head.pushClosure (source.holds stack))
  | .make factory argument => do
      need (static.callAdmitted stack factory argument && argument.admitted stack)
      let head ← stack.head?
      need (head.closures.length < maximumClosures)
      return setHead stack (head.pushClosure false)
  | .discard factory argument => do
      need (static.callAdmitted stack factory argument && argument.admitted stack)
      return stack
  | .relambda target body result => do
      need (target.admitted stack)
      let holds ← Stmt.lambdaCheck? static stack body result
      need (!(inBody stack && holds))
      return setHolds stack target holds
  | .realias target source => do
      need (target.admitted stack && source.admitted stack && !(inBody stack && source.holds stack))
      return setHolds stack target (source.holds stack)
  | .remake target factory argument => do
      need (target.admitted stack && static.callAdmitted stack factory argument && argument.admitted stack)
      return setHolds stack target false
  | .observe observed => do
      need (stack.length == 1 && (stack.head?.map (·.kind == .run)).getD false && observed.admitted stack)
      return stack
  | .loop count body => do
      need (stack.length == 1 && (stack.head?.map (·.kind == .run)).getD false)
      need (1 ≤ count && count ≤ maximumLoop && !body.isEmpty && body.length ≤ maximumLoopBody)
      need (body.all Stmt.loopStatement)
      let after ← Stmt.listCheck? static stack body
      return after

/-- Check statements in order. -/
def Stmt.listCheck? (static : Static) (stack : List Scope) : List Stmt → Option (List Scope)
  | [] => some stack
  | stmt :: rest => do
      let next ← stmt.check? static stack
      Stmt.listCheck? static next rest

/-- Check a lambda created in the head scope and say whether it captures a
closure. Its body is a new scope; it neither observes nor loops. It captures no
closure that captures a closure: the pin rejects such chains with `SC0422`. -/
def Stmt.lambdaCheck? (static : Static) (stack : List Scope) (body : List Stmt) (result : Term) :
    Option Bool := do
  let lambdas := stack.filter (·.kind == .lambda)
  need (lambdas.length < maximumDepth && body.length ≤ maximumBody)
  need ((lambdaCaps body result).all fun cap => match cap with
    | .closure up index => !(Ref.holds stack ⟨up, index⟩)
    | _ => true)
  let inner ← Stmt.listCheck? static ({kind := .lambda} :: stack) body
  need (result.admitted inner)
  return lambdaHolds body result
end

/-- A factory's own statements name the field, run a checked operation or call
a closure. -/
def Factory.effectful (factory : Factory) : Bool :=
  factory.body.any fun stmt => (match stmt with | .assign .field _ => true | _ => false) ||
    stmt.ownTerms.any Term.effectful

/-- A factory returns one of its closures, or a lambda that captures one. -/
def Factory.returnsLocal (factory : Factory) : Bool :=
  match factory.returns with
  | .closure _ => true
  | .lambda body result => lambdaHolds body result

/-- Check factory `index` in its own scope, given the earlier factories, and
give its method flag and whether it returns one of its own closures. Its result
never captures a closure, and a factory that returns one of its closures has no
effect of its own: the pin rejects both forms with `SC0422`. -/
def Factory.info? (info : List (Bool × Bool)) (index : Nat) (factory : Factory) : Option (Bool × Bool) := do
  need (info.length == index && factory.body.length ≤ maximumFactorySteps)
  need (!(factory.returnsLocal && factory.effectful))
  let static : Static := {factories := info ++ [(factory.method, false)], within := some index}
  let stack ← Stmt.listCheck? static [Scope.ofFactory factory] factory.body
  let holds ← match factory.returns with
    | .closure closure => do
        let scope ← stack.head?
        need (closure < scope.closures.length)
        pure (scope.closures.getD closure false)
    | .lambda body result => Stmt.lambdaCheck? static stack body result
  need (!holds)
  return (factory.method, factory.returnsLocal)

/-- Check every factory in order. -/
def Plan.factoryInfo? (plan : Plan) : Option (List (Bool × Bool)) := do
  need (plan.factories.length ≤ maximumFactories)
  let mut info : List (Bool × Bool) := []
  for (factory, index) in plan.factories.zipIdx do
    info := info ++ [← factory.info? info index]
  return info

/-- The scopes of `run` after its steps, when the plan is admitted. -/
def Plan.scan? (plan : Plan) : Option (List Scope) := do
  let info ← plan.factoryInfo?
  need (!plan.steps.isEmpty && plan.steps.length ≤ maximumSteps)
  Stmt.listCheck? {factories := info} [{kind := .run}] plan.steps

mutual
def Stmt.observes : Stmt → Bool
  | .observe _ => true
  | .loop _ body => Stmt.listObserves body
  | _ => false

def Stmt.listObserves : List Stmt → Bool
  | [] => false
  | stmt :: rest => stmt.observes || Stmt.listObserves rest
end

mutual
/-- A statement, or a statement in a lambda it creates, calls a factory. -/
def Stmt.makes : Stmt → Bool
  | .make .. | .discard .. | .remake .. => true
  | .lambda body _ | .relambda _ body _ => Stmt.listMakes body
  | .loop _ body => Stmt.listMakes body
  | _ => false

def Stmt.listMakes : List Stmt → Bool
  | [] => false
  | stmt :: rest => stmt.makes || Stmt.listMakes rest
end

namespace Plan

def observes (plan : Plan) : Bool := Stmt.listObserves plan.steps

def common (plan : Plan) : Bool := plan.scan?.isSome && plan.observes

/-- `runtime-closure-captures`: closures of one body, no factory. -/
def capturesAdmitted (plan : Plan) : Bool := plan.factories.isEmpty && plan.common

/-- `runtime-closure-factories`: at least one factory, called from `run` or one
of its lambdas. -/
def factoriesAdmitted (plan : Plan) : Bool :=
  !plan.factories.isEmpty && Stmt.listMakes plan.steps && plan.common

end Plan

/-! Traversal. -/

/-- A statement where it occurs: its lambda depth, 0 in `run` or a factory's
body, whether it is in a factory or a loop, and the statements before it in
its scope, last first. -/
structure Visit where
  stmt : Stmt
  lambda : Nat
  factory : Bool
  loop : Bool
  before : List Stmt

mutual
def Stmt.visits (lambda : Nat) (factory loop : Bool) (before : List Stmt) : Stmt → List Visit
  | stmt@(.lambda body _) | stmt@(.relambda _ body _) =>
      ⟨stmt, lambda, factory, loop, before⟩ :: Stmt.listVisits (lambda + 1) factory false [] body
  | stmt@(.loop _ body) => ⟨stmt, lambda, factory, loop, before⟩ :: Stmt.listVisits lambda factory true before body
  | stmt => [⟨stmt, lambda, factory, loop, before⟩]

def Stmt.listVisits (lambda : Nat) (factory loop : Bool) (before : List Stmt) : List Stmt → List Visit
  | [] => []
  | stmt :: rest => stmt.visits lambda factory loop before ++ Stmt.listVisits lambda factory loop (stmt :: before) rest
end

def Returns.stmt? : Returns → Option Stmt
  | .closure _ => none
  | .lambda body result => some (.lambda body result)

/-- Every statement of a plan: `run`'s, then each factory's with the lambda it
returns. -/
def Plan.visits (plan : Plan) : List Visit :=
  Stmt.listVisits 0 false false [] plan.steps ++ plan.factories.flatMap fun factory =>
    Stmt.listVisits 0 true false [] (factory.body ++ factory.returns.stmt?.toList)

/-- The terms a statement holds itself, without those of a lambda body. -/
def Stmt.terms : Stmt → List Term
  | .value init => [init]
  | .assign _ assigned => [assigned]
  | .lambda _ result | .relambda _ _ result => [result]
  | .make _ argument | .discard _ argument | .remake _ _ argument => [argument]
  | .observe observed => [observed]
  | _ => []

def Term.subterms (term : Term) : List Term :=
  term :: match term with
    | .lit _ | .var _ => []
    | .op _ left right | .checked _ left right => left.subterms ++ right.subterms
    | .call _ _ argument => argument.subterms

def Term.via? : Term → Option Via
  | .call via .. => some via
  | _ => none

def Term.isChecked : Term → Bool
  | .checked .. => true
  | _ => false

namespace Plan

def terms (plan : Plan) : List Term := plan.visits.flatMap fun visit => visit.stmt.terms.flatMap Term.subterms

def usesVia (plan : Plan) (via : Via) : Bool := plan.terms.any (·.via? == some via)

def usesField (plan : Plan) : Bool :=
  plan.terms.any (· == .var .field) || plan.visits.any fun visit => match visit.stmt with
    | .assign .field _ => true
    | _ => false

end Plan

/-! The interpreter: the same semantics over Lean numbers and closure values,
for shapes, generation filters and the validators' model. -/

/-- A closure value: its lambda and the scopes it captured, innermost first, as
they were when it was created. -/
inductive Closure where
  | mk (body : List Stmt) (result : Term) (params : List Nat) (values : List (List Nat))
      (closures : List (List Closure))
  deriving Inhabited

/-- The scopes a statement runs in, innermost first. -/
structure Frames where
  params : List Nat
  values : List (List Nat)
  closures : List (List Closure)
  deriving Inhabited

inductive Outcome where
  | word (value : Nat)
  | panic (code : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Where a panic was raised: in `run`'s own statements, in a factory's, or in
a lambda body. -/
inductive Stop where
  | panic (code : Nat) (site : String)
  | fuel

structure Machine where
  field : Nat := 0
  fold : Nat := 0

abbrev Run := StateT Machine (Except Stop)

def Op.apply : Op → Nat → Nat → Nat
  | .add, left, right => (left + right) % modulus
  | .sub, left, right => (left + modulus - right) % modulus
  | .mul, left, right => (left * right) % modulus
  | .xor, left, right => left ^^^ right

namespace Frames

def close (frames : Frames) (body : List Stmt) (result : Term) : Closure :=
  .mk body result frames.params frames.values frames.closures

def closureAt (frames : Frames) (ref : Ref) : Closure := (frames.closures.getD ref.up []).getD ref.index default

def pushValue (frames : Frames) (value : Nat) : Frames :=
  {frames with values := frames.values.modify 0 (· ++ [value])}

def pushClosure (frames : Frames) (closure : Closure) : Frames :=
  {frames with closures := frames.closures.modify 0 (· ++ [closure])}

def setClosure (frames : Frames) (ref : Ref) (closure : Closure) : Frames :=
  {frames with closures := frames.closures.modify ref.up (·.set ref.index closure)}

def read (frames : Frames) : Var → Run Nat
  | .param up => pure (frames.params.getD up 0)
  | .value ref => pure ((frames.values.getD ref.up []).getD ref.index 0)
  | .field => return (← get).field

def write (frames : Frames) (value : Nat) : Var → Run Frames
  | .param up => pure {frames with params := frames.params.set up value}
  | .value ref => pure {frames with values := frames.values.modify ref.up (·.set ref.index value)}
  | .field => do
      modify fun machine => {machine with field := value}
      return frames

end Frames

mutual
def evalTerm (plan : Plan) : Nat → String → Frames → Term → Run Nat
  | 0, _, _, _ => throw .fuel
  | _ + 1, _, _, .lit value => pure (value % modulus)
  | _ + 1, _, frames, .var var => frames.read var
  | fuel + 1, site, frames, .op op left right => do
      let first ← evalTerm plan fuel site frames left
      let second ← evalTerm plan fuel site frames right
      return op.apply first second
  | fuel + 1, site, frames, .checked op left right => do
      let first ← evalTerm plan fuel site frames left
      let second ← evalTerm plan fuel site frames right
      match op with
      | .add => if first + second < modulus then return first + second else throw (.panic 0x11 site)
      | .div => if second = 0 then throw (.panic 0x12 site) else return first / second
  | fuel + 1, site, frames, .call via ref argument => do
      let closure := frames.closureAt ref
      let value ← evalTerm plan fuel site frames argument
      match via with
      | .twice => do
          let once ← callClosure plan fuel closure value
          callClosure plan fuel closure once
      | _ => callClosure plan fuel closure value

/-- A call starts from the captured scopes and the argument, so whatever its
body writes stays in this call. -/
def callClosure (plan : Plan) : Nat → Closure → Nat → Run Nat
  | 0, _, _ => throw .fuel
  | fuel + 1, .mk body result params values closures, argument => do
      let frames : Frames := {params := argument :: params, values := [] :: values, closures := [] :: closures}
      let frames ← execStmts plan fuel "body" frames body
      evalTerm plan fuel "body" frames result

def execStmts (plan : Plan) : Nat → String → Frames → List Stmt → Run Frames
  | 0, _, _, _ => throw .fuel
  | _ + 1, _, frames, [] => pure frames
  | fuel + 1, site, frames, stmt :: rest => do
      let frames ← execStmt plan fuel site frames stmt
      execStmts plan fuel site frames rest

def execStmt (plan : Plan) : Nat → String → Frames → Stmt → Run Frames
  | 0, _, _, _ => throw .fuel
  | fuel + 1, site, frames, .value init => do
      return frames.pushValue (← evalTerm plan fuel site frames init)
  | fuel + 1, site, frames, .assign target value => do
      frames.write (← evalTerm plan fuel site frames value) target
  | _ + 1, _, frames, .lambda body result => pure (frames.pushClosure (frames.close body result))
  | _ + 1, _, frames, .alias source => pure (frames.pushClosure (frames.closureAt source))
  | fuel + 1, site, frames, .make factory argument => do
      let value ← evalTerm plan fuel site frames argument
      return frames.pushClosure (← makeFactory plan fuel factory value)
  | fuel + 1, site, frames, .discard factory argument => do
      let value ← evalTerm plan fuel site frames argument
      let _ ← makeFactory plan fuel factory value
      return frames
  | _ + 1, _, frames, .relambda target body result => pure (frames.setClosure target (frames.close body result))
  | _ + 1, _, frames, .realias target source => pure (frames.setClosure target (frames.closureAt source))
  | fuel + 1, site, frames, .remake target factory argument => do
      let value ← evalTerm plan fuel site frames argument
      return frames.setClosure target (← makeFactory plan fuel factory value)
  | fuel + 1, site, frames, .observe value => do
      let observed ← evalTerm plan fuel site frames value
      modify fun machine => {machine with fold := ((machine.fold * foldPrime) % modulus) ^^^ observed}
      return frames
  | fuel + 1, site, frames, .loop count body => loopRun plan fuel site frames count body

def loopRun (plan : Plan) : Nat → String → Frames → Nat → List Stmt → Run Frames
  | 0, _, _, _, _ => throw .fuel
  | _ + 1, _, frames, 0, _ => pure frames
  | fuel + 1, site, frames, count + 1, body => do
      let frames ← execStmts plan fuel site frames body
      loopRun plan fuel site frames count body

/-- A factory runs in a scope of its own: its parameter and locals. -/
def makeFactory (plan : Plan) : Nat → Nat → Nat → Run Closure
  | 0, _, _ => throw .fuel
  | fuel + 1, index, argument => do
      let factory := plan.factories.getD index default
      let frames : Frames := {params := [argument], values := [[]], closures := [[]]}
      let frames ← execStmts plan fuel "factory" frames factory.body
      match factory.returns with
      | .closure closure => return frames.closureAt ⟨0, closure⟩
      | .lambda body result => return frames.close body result
end

def interpreterFuel : Nat := 100000

namespace Plan

/-- The outcome at an input, and the site of a panic. -/
def run (plan : Plan) (input : Nat) : Outcome × Option String :=
  let frames : Frames := {params := [input % modulus], values := [[]], closures := [[]]}
  match (execStmts plan interpreterFuel "run" frames plan.steps).run {} with
  | .ok (_, machine) => (.word machine.fold, none)
  | .error (.panic code site) => (.panic code, some site)
  | .error .fuel => (.panic 0, some "fuel")

def outcome (plan : Plan) (input : Nat) : Outcome := (plan.run input).1

end Plan

/-! The reference compiler. -/

private def num (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- A closure's Core type: a call returns its Word or passes revert data on. -/
def fnTy : Ty := .function .word Integers.resultType

/-- The cells of one scope by de Bruijn level. -/
structure Cells where
  param : Nat
  values : List Nat := []
  closures : List Nat := []
  deriving Inhabited

/-- No binder has this level, so a stray reference fails the full checker. -/
def absent : Nat := 1000000

/-- A binder by level; an unbound level gives an index past every binder. -/
def slot (env : Env) (level : Nat) : Expr :=
  if level < env.depth then env.ref level else .var (env.depth + absent)

/-- The shared cells: the contract field and the fold. -/
structure Ctx where
  plan : Plan
  field : Nat
  fold : Nat

namespace Cells

def paramOf (stack : List Cells) (up : Nat) : Nat := ((stack[up]?).map (·.param)).getD absent

def valueOf (stack : List Cells) (ref : Ref) : Nat := ((stack[ref.up]?).bind (·.values[ref.index]?)).getD absent

def closureOf (stack : List Cells) (ref : Ref) : Nat := ((stack[ref.up]?).bind (·.closures[ref.index]?)).getD absent

def varOf (ctx : Ctx) (stack : List Cells) : Var → Nat
  | .param up => paramOf stack up
  | .value ref => valueOf stack ref
  | .field => ctx.field

def capOf (stack : List Cells) : Cap → Nat
  | .param up => paramOf stack up
  | .value up index => valueOf stack ⟨up, index⟩
  | .closure up index => closureOf stack ⟨up, index⟩

def capTy : Cap → Ty
  | .closure .. => fnTy
  | _ => .word

def pushValue (stack : List Cells) (cell : Nat) : List Cells :=
  stack.modify 0 fun cells => {cells with values := cells.values ++ [cell]}

def pushClosure (stack : List Cells) (cell : Nat) : List Cells :=
  stack.modify 0 fun cells => {cells with closures := cells.closures ++ [cell]}

/-- A body's scopes: its own, then the enclosing ones with each captured local
at its fresh per-call cell and every other local absent. -/
def body (stack : List Cells) (caps : List (Cap × Nat)) (param : Nat) : List Cells :=
  let hidden := stack.map fun cells =>
    ({param := absent, values := cells.values.map fun _ => absent, closures := cells.closures.map fun _ => absent} :
      Cells)
  let enclosing := caps.foldl (init := hidden) fun stack (cap, cell) => match cap with
    | .param up => stack.modify up fun cells => {cells with param := cell}
    | .value up index => stack.modify up fun cells => {cells with values := cells.values.set index cell}
    | .closure up index => stack.modify up fun cells => {cells with closures := cells.closures.set index cell}
  {param} :: enclosing

end Cells

private def opExpr : Op → Expr → Expr → Expr
  | .add, left, right => .binary .wordAdd left right
  | .sub, left, right => .binary .wordSub left right
  | .mul, left, right => .binary .wordMul left right
  | .xor, left, right => .binary .wordXor left right

/-- Bind each item's expression in order and continue with their levels. -/
def bindAll {α : Type} (env : Env) (items : List α) (expr : Env → α → Expr) (rest : Env → List Nat → Expr) : Expr :=
  match items with
  | [] => rest env []
  | item :: more => env.bind (expr env item) fun env level =>
      bindAll env more expr fun env levels => rest env (level :: levels)

mutual
def term (ctx : Ctx) : Nat → List Cells → Env → Term → (Env → Nat → Expr) → Expr
  | 0, _, _, _, _ => .unit
  | _ + 1, _, env, .lit value, rest => env.bind (num value) rest
  | _ + 1, stack, env, .var var, rest => env.bind (.loadCell (slot env (Cells.varOf ctx stack var))) rest
  | fuel + 1, stack, env, .op op left right, rest =>
      term ctx fuel stack env left fun env first =>
      term ctx fuel stack env right fun env second =>
        env.bind (opExpr op (slot env first) (slot env second)) rest
  | fuel + 1, stack, env, .checked op left right, rest =>
      term ctx fuel stack env left fun env first =>
      term ctx fuel stack env right fun env second =>
        Integers.operation IntType.uint256 false (if op == .add then .add else .div) env
          (fun env => slot env first) (fun env => slot env second) rest
  | fuel + 1, stack, env, .call via ref argument, rest =>
      term ctx fuel stack env argument fun env value =>
        let cell := Cells.closureOf stack ref
        let once (env : Env) (argument : Nat) (next : Env → Nat → Expr) : Expr :=
          .caseE (.apply (.loadCell (slot env cell)) (slot env argument))
            (next {env with depth := env.depth + 1} env.depth) (.inRight .word (.var 0))
        match via with
        | .twice => once env value fun env first => once env first rest
        | _ => once env value rest

def stmts (ctx : Ctx) : Nat → List Cells → Env → List Stmt → (List Cells → Env → Expr) → Expr
  | 0, _, _, _, _ => .unit
  | _ + 1, stack, env, [], rest => rest stack env
  | fuel + 1, stack, env, head :: more, rest =>
      stmt ctx fuel stack env head fun stack env => stmts ctx fuel stack env more rest

def stmt (ctx : Ctx) : Nat → List Cells → Env → Stmt → (List Cells → Env → Expr) → Expr
  | 0, _, _, _, _ => .unit
  | fuel + 1, stack, env, .value init, rest =>
      term ctx fuel stack env init fun env value =>
        env.bind (.newCell .word (slot env value)) fun env cell => rest (Cells.pushValue stack cell) env
  | fuel + 1, stack, env, .assign target value, rest =>
      term ctx fuel stack env value fun env value =>
        env.bind (.storeCell (slot env (Cells.varOf ctx stack target)) (slot env value)) fun env _ => rest stack env
  | fuel + 1, stack, env, .lambda body result, rest =>
      closure ctx fuel stack env body result fun env value =>
        env.bind (.newCell fnTy (slot env value)) fun env cell => rest (Cells.pushClosure stack cell) env
  | _ + 1, stack, env, .alias source, rest =>
      env.bind (.newCell fnTy (.loadCell (slot env (Cells.closureOf stack source)))) fun env cell =>
        rest (Cells.pushClosure stack cell) env
  | fuel + 1, stack, env, .make index argument, rest =>
      term ctx fuel stack env argument fun env value =>
        factory ctx fuel env index value fun env made =>
          env.bind (.newCell fnTy (slot env made)) fun env cell => rest (Cells.pushClosure stack cell) env
  | fuel + 1, stack, env, .discard index argument, rest =>
      term ctx fuel stack env argument fun env value =>
        factory ctx fuel env index value fun env _ => rest stack env
  | fuel + 1, stack, env, .relambda target body result, rest =>
      closure ctx fuel stack env body result fun env value =>
        env.bind (.storeCell (slot env (Cells.closureOf stack target)) (slot env value)) fun env _ => rest stack env
  | _ + 1, stack, env, .realias target source, rest =>
      env.bind (.storeCell (slot env (Cells.closureOf stack target))
        (.loadCell (slot env (Cells.closureOf stack source)))) fun env _ => rest stack env
  | fuel + 1, stack, env, .remake target index argument, rest =>
      term ctx fuel stack env argument fun env value =>
        factory ctx fuel env index value fun env made =>
          env.bind (.storeCell (slot env (Cells.closureOf stack target)) (slot env made)) fun env _ => rest stack env
  | fuel + 1, stack, env, .observe value, rest =>
      term ctx fuel stack env value fun env value =>
        env.bind (.storeCell (slot env ctx.fold) (.binary .wordXor
          (.binary .wordMul (.loadCell (slot env ctx.fold)) (num foldPrime)) (slot env value))) fun env _ =>
            rest stack env
  | fuel + 1, stack, env, .loop count body, rest => unroll ctx fuel stack env count body rest

def unroll (ctx : Ctx) : Nat → List Cells → Env → Nat → List Stmt → (List Cells → Env → Expr) → Expr
  | 0, _, _, _, _, _ => .unit
  | _ + 1, stack, env, 0, _, rest => rest stack env
  | fuel + 1, stack, env, count + 1, body, rest =>
      stmts ctx fuel stack env body fun stack env => unroll ctx fuel stack env count body rest

/-- A lambda created in the head scope: snapshots of what it captures, then a
Core lambda that copies each snapshot into a fresh cell at every call. -/
def closure (ctx : Ctx) : Nat → List Cells → Env → List Stmt → Term → (Env → Nat → Expr) → Expr
  | 0, _, _, _, _, _ => .unit
  | fuel + 1, stack, env, body, result, rest =>
      let caps := lambdaCaps body result
      bindAll env caps (fun env cap => .loadCell (slot env (Cells.capOf stack cap))) fun env snapshots =>
        let inner : Env := {env with depth := env.depth + 1}
        let argument := env.depth
        let core := inner.bind (.newCell .word (slot inner argument)) fun env param =>
          bindAll env (caps.zip snapshots) (fun env (cap, snapshot) => .newCell (Cells.capTy cap) (slot env snapshot))
            fun env cells =>
              stmts ctx fuel (Cells.body stack (caps.zip cells) param) env body fun stack env =>
                term ctx fuel stack env result fun env value => .inLeft payloadType (slot env value)
        env.bind (.lambda .word Integers.resultType core) rest

/-- A factory runs where it is called, in a scope of its own. -/
def factory (ctx : Ctx) : Nat → Env → Nat → Nat → (Env → Nat → Expr) → Expr
  | 0, _, _, _, _ => .unit
  | fuel + 1, env, index, argument, rest =>
      match ctx.plan.factories[index]? with
      | none => .unit
      | some made =>
          env.bind (.newCell .word (slot env argument)) fun env param =>
            stmts ctx fuel [{param}] env made.body fun stack env =>
              match made.returns with
              | .closure index => env.bind (.loadCell (slot env (Cells.closureOf stack ⟨0, index⟩))) rest
              | .lambda body result => closure ctx fuel stack env body result rest
end

def referenceFuel : Nat := 100000

namespace Plan

/-- `run` as a Core lambda of the input Word: the field, the fold and `sc_x`
are cells, and the result is the fold or the revert data. -/
def expression (plan : Plan) : Expr :=
  let env : Env := {depth := 1}
  .lambda .word Integers.resultType (
    env.bind (.newCell .word (num 0)) fun env field =>
    env.bind (.newCell .word (num 0)) fun env fold =>
    env.bind (.newCell .word (slot env 0)) fun env input =>
      stmts {plan, field, fold} referenceFuel [{param := input}] env plan.steps fun _ env =>
        .inLeft payloadType (.loadCell (slot env fold)))

def program (plan : Plan) : Program := {
  resultType := .function .word Integers.resultType
  dataDefinitions := []
  body := plan.expression }

def applied (plan : Plan) (input : Word) : Program := {
  resultType := Integers.resultType
  dataDefinitions := []
  body := .apply plan.expression (.word input) }

def nodes (plan : Plan) : Nat := programNodes (plan.applied Word.zero)

end Plan

/-! Shapes: what a plan exercises, for coverage. -/

private def sorted (values : List String) : List String := (values.eraseDups.toArray.qsort (· < ·)).toList

def Stmt.lambdaParts? : Stmt → Option (List Stmt × Term)
  | .lambda body result | .relambda _ body result => some (body, result)
  | _ => none

/-- A capture by the scope it comes from: `run`'s input or a factory's
parameter, a lambda's parameter, a Word local of `run` or a factory, one of a
lambda body, or a closure. -/
def Cap.shape (visit : Visit) : Cap → String
  | .param up => if visit.lambda = up then (if visit.factory then "param" else "input") else "arg"
  | .value up _ => if visit.lambda = up then "value" else "body-value"
  | .closure .. => "closure"

/-- An earlier lambda of the scope captured this local. -/
def capturedBefore (before : List Stmt) (cap : Cap) : Bool :=
  before.any fun stmt => match stmt.lambdaParts? with
    | some (body, result) => (lambdaCaps body result).contains cap
    | none => false

def Term.mentionsField (term : Term) : Bool := term.subterms.contains (.var .field)

namespace Plan

def captureShapes (plan : Plan) : List String := sorted (plan.visits.flatMap fun visit =>
  match visit.stmt.lambdaParts? with
  | some (body, result) =>
      let caps := lambdaCaps body result
      if caps.isEmpty then ["nothing"] else caps.map (Cap.shape visit)
  | none => [])

def fieldShapes (plan : Plan) : List String := sorted (plan.visits.flatMap fun visit =>
  let place := if visit.lambda > 0 then "body" else if visit.factory then "factory" else "run"
  let reads := if visit.stmt.terms.any Term.mentionsField then [place ++ "-read"] else []
  let writes := match visit.stmt with
    | .assign .field _ => [place ++ "-write"]
    | _ => []
  reads ++ writes)

def writeShapes (plan : Plan) : List String := sorted (plan.visits.filterMap fun visit =>
  if visit.lambda = 0 then none else match visit.stmt with
    | .assign (.param up) _ => some (if up = 0 then "own-param" else "captured-param")
    | .assign (.value ref) _ => some (if ref.up = 0 then "own-value" else "captured-value")
    | .relambda target .. | .realias target _ | .remake target .. =>
        some (if target.up = 0 then "own-closure" else "captured-closure")
    | _ => none)

/-- A write to a local, or a rebinding of a closure, that an earlier lambda of
the same scope captured. -/
def outerShapes (plan : Plan) : List String := sorted (plan.visits.filterMap fun visit => match visit.stmt with
  | .assign (.param 0) _ => if capturedBefore visit.before (.param 0) then some "later-write" else none
  | .assign (.value ⟨0, index⟩) _ => if capturedBefore visit.before (.value 0 index) then some "later-write" else none
  | .relambda ⟨0, index⟩ .. | .realias ⟨0, index⟩ _ | .remake ⟨0, index⟩ .. =>
      if capturedBefore visit.before (.closure 0 index) then some "later-rebind" else none
  | _ => none)

def calls (visit : Visit) : List (Via × Ref) := (visit.stmt.terms.flatMap Term.subterms).filterMap fun term =>
  match term with
  | .call via ref _ => some (via, ref)
  | _ => none

/-- How closures are called; `repeat` when one closure of `run` is called at two
sites, twice, or in a loop. -/
def callShapes (plan : Plan) : List String :=
  let sites := plan.visits.flatMap fun visit => (calls visit).flatMap fun (via, ref) =>
    [match via with | .direct => "direct" | .apply => "apply" | .twice => "twice"] ++
    (if visit.loop then ["loop", "repeat"] else []) ++ (if visit.lambda > 0 then ["in-body"] else []) ++
    (if visit.lambda > 0 && ref.up > 0 then ["captured"] else []) ++ (if via == .twice then ["repeat"] else [])
  let own := plan.visits.flatMap fun visit =>
    if visit.lambda = 0 && !visit.factory then (calls visit).filterMap fun (_, ref) =>
      if ref.up = 0 then some ref.index else none
    else []
  let repeated := own.any fun index => own.count index ≥ 2
  sorted (sites ++ if repeated then ["repeat"] else [])

def closureShapes (plan : Plan) : List String := sorted (plan.visits.filterMap fun visit => match visit.stmt with
  | .lambda .. => some (if visit.lambda > 0 then "nested" else "lambda")
  | .alias _ => some "alias"
  | .relambda .. => some "relambda"
  | .realias .. => some "realias"
  | .make .. => some "make"
  | .discard .. => some "discard"
  | .remake .. => some "remake"
  | .loop .. => some "loop"
  | _ => none)

def factoryArgument? : Stmt → Option (Nat × Term)
  | .make index argument | .discard index argument | .remake _ index argument => some (index, argument)
  | _ => none

/-- What factories do and how they are called. -/
def factoryShapes (plan : Plan) : List String :=
  let own := plan.factories.flatMap fun factory =>
    let visits := Stmt.listVisits 0 true false [] factory.body
    let direct := visits.filter (·.lambda = 0)
    [if factory.method then "method" else "free",
      match factory.returns with | .closure _ => "closure-result" | .lambda .. => "lambda-result"] ++
    (if direct.any (·.stmt.ownTerms.any (·.subterms.any Term.isChecked)) then ["checked-effect"] else []) ++
    (if direct.any (fun visit => (factoryArgument? visit.stmt).isSome) then ["chained"] else [])
  let factoryVisits := plan.visits.filter (·.factory)
  let captures := factoryVisits.flatMap fun visit => match visit.stmt.lambdaParts? with
    | some (body, result) => (lambdaCaps body result).filterMap fun cap => match Cap.shape visit cap with
        | "param" => some "captures-param"
        | "value" => some "captures-value"
        | _ => none
    | none => []
  let laterWrite := if factoryVisits.any (fun visit => match visit.stmt with
      | .assign (.param 0) _ => capturedBefore visit.before (.param 0)
      | .assign (.value ⟨0, index⟩) _ => capturedBefore visit.before (.value 0 index)
      | _ => false) then ["later-write"] else []
  let made := (plan.visits.filter (!·.factory)).filterMap fun visit =>
    (factoryArgument? visit.stmt).map fun (index, argument) => (index, argument, visit.lambda)
  let callers := made.flatMap fun (_, argument, lambda) =>
    [match argument with | .lit _ => "literal-argument" | _ => "runtime-argument"] ++
    (if lambda > 0 then ["in-body"] else [])
  let instances := if made.any (fun (index, _, _) => (made.filter (·.1 == index)).length ≥ 2) then ["instances"] else []
  sorted (own ++ captures ++ laterWrite ++ callers ++ instances)

def boundaryRuns (plan : Plan) : List (Outcome × Option String) := Integers.boundaryWords.map plan.run

def outcomeName : Outcome → String
  | .word _ => "return"
  | .panic 0x11 => "panic-0x11"
  | .panic 0x12 => "panic-0x12"
  | .panic _ => "panic-other"

def shapes (factories : Bool) (plan : Plan) : List (String × List String) :=
  let runs := plan.boundaryRuns
  [("capture", plan.captureShapes), ("field", plan.fieldShapes), ("write", plan.writeShapes),
    ("outer", plan.outerShapes), ("call", plan.callShapes), ("closure", plan.closureShapes)] ++
  (if factories then [("factory", plan.factoryShapes)] else []) ++
  [("outcome", sorted (runs.map (outcomeName ·.1))), ("panicSite", sorted (runs.filterMap (·.2)))]

def capturesShapes (plan : Plan) : List (String × List String) := plan.shapes false

def factoriesShapes (plan : Plan) : List (String × List String) := plan.shapes true

end Plan

/-- Every value a fixed corpus of a profile requires, by dimension. -/
def capturesInventory : List (String × List String) := [
  ("capture", ["arg", "body-value", "closure", "input", "nothing", "value"]),
  ("field", ["body-read", "body-write", "run-read", "run-write"]),
  ("write", ["captured-closure", "captured-param", "captured-value", "own-closure", "own-param", "own-value"]),
  ("outer", ["later-rebind", "later-write"]),
  ("call", ["apply", "captured", "direct", "in-body", "loop", "repeat", "twice"]),
  ("closure", ["alias", "lambda", "loop", "nested", "realias", "relambda"]),
  ("outcome", ["panic-0x11", "panic-0x12", "return"]),
  ("panicSite", ["body", "run"])]

def factoriesInventory : List (String × List String) := [
  ("capture", ["arg", "body-value", "closure", "input", "nothing", "param", "value"]),
  ("field", ["body-read", "body-write", "factory-read", "factory-write", "run-read", "run-write"]),
  ("write", ["captured-closure", "captured-param", "captured-value", "own-closure", "own-param", "own-value"]),
  ("outer", ["later-rebind", "later-write"]),
  ("call", ["apply", "captured", "direct", "in-body", "loop", "repeat", "twice"]),
  ("closure", ["alias", "discard", "lambda", "loop", "make", "nested", "realias", "relambda", "remake"]),
  ("factory", ["captures-param", "captures-value", "chained", "checked-effect", "closure-result", "free",
    "in-body", "instances", "lambda-result", "later-write", "literal-argument", "method", "runtime-argument"]),
  ("outcome", ["panic-0x11", "panic-0x12", "return"]),
  ("panicSite", ["body", "factory", "run"])]

/-! Generation: a SplitMix64 stream of the case seed, one domain per profile.
Each statement is drawn against the scopes so far and kept only if it checks,
so a drawn plan refers only to declared locals. -/

def capturesDomain : UInt64 := 0x636c6f7375726501
def factoriesDomain : UInt64 := 0x636c6f6661637401

def pick {α : Type} [Inhabited α] (items : List α) : Gen α := do return items.getD (← draw items.length) default

/-- The Words a scope can name: parameters, Word locals and the field. -/
def visibleVars (stack : List Scope) : List Var :=
  (List.range stack.length).map Var.param ++
  (stack.zipIdx.flatMap fun (scope, up) => (List.range scope.values).map fun index => Var.value ⟨up, index⟩) ++
  (if Static.fieldVisible stack then [.field] else [])

def visibleClosures (stack : List Scope) : List (Ref × Bool) :=
  stack.zipIdx.flatMap fun (scope, up) => scope.closures.zipIdx.map fun (holds, index) => (⟨up, index⟩, holds)

def drawLeaf (stack : List Scope) : Gen Term := do
  let vars := visibleVars stack
  if vars.isEmpty || (← draw 4) == 0 then return .lit (← pick literals)
  return .var (← pick vars)

def drawVia (holds : Bool) : Gen Via := if holds then pure .direct else pick [Via.direct, .direct, .apply, .twice]

def drawTerm (stack : List Scope) : Nat → Gen Term
  | 0 => drawLeaf stack
  | depth + 1 => do
      let closures := visibleClosures stack
      match ← drawWeighted [3, 3, 1, if closures.isEmpty then 0 else 3] with
      | 0 => drawLeaf stack
      | 1 => return .op (← pick [Op.add, .add, .sub, .mul, .xor]) (← drawTerm stack depth) (← drawTerm stack depth)
      | 2 => do
          let op ← pick [Checked.add, .add, .div]
          let left ← drawTerm stack depth
          let right ← if op == .div && (← draw 2) == 0 then pure (.lit (← pick [1, 2, 3, 7])) else drawTerm stack depth
          return .checked op left right
      | _ => do
          let (ref, holds) ← pick closures
          return .call (← drawVia holds) ref (← drawTerm stack depth)

/-- A call of a visible closure, or a term when there is none. -/
def drawCall (stack : List Scope) : Gen Term := do
  let closures := visibleClosures stack
  if closures.isEmpty then drawTerm stack 2 else
    let (ref, holds) ← pick closures
    return .call (← drawVia holds) ref (← drawTerm stack 1)

/-- An assignment target, a captured local half the time when there is one. -/
def drawTarget (stack : List Scope) : Gen Var := do
  let vars := visibleVars stack
  let captured := vars.filter fun var => match var with
    | .value ref => ref.up > 0
    | .param up => up > 0
    | .field => false
  if !captured.isEmpty && (← draw 2) == 0 then pick captured else pick vars

def drawArgument (stack : List Scope) : Gen Term := do
  if (← draw 2) == 0 then return .lit (← pick literals) else drawTerm stack 1

/-- The factories a scope may call. -/
def callable (static : Static) (stack : List Scope) : List Nat :=
  (List.range static.factories.length).filter (static.factoryAdmitted stack ·)

def lambdaDepth (stack : List Scope) : Nat := (stack.filter (·.kind == .lambda)).length

mutual
def drawLambda (static : Static) (stack : List Scope) : Nat → Gen (List Stmt × Term)
  | 0 => return ([], .lit 0)
  | fuel + 1 => do
      let count ← draw (maximumBody + 1)
      let (body, inner) ← drawBlock static ({kind := .lambda} :: stack) fuel count []
      return (body, ← drawTerm inner 2)

/-- Draw `count` statements of a lambda body or a factory, each kept if it
checks. -/
def drawBlock (static : Static) (stack : List Scope) : Nat → Nat → List Stmt → Gen (List Stmt × List Scope)
  | 0, _, done => return (done.reverse, stack)
  | _ + 1, 0, done => return (done.reverse, stack)
  | fuel + 1, count + 1, done => do
      let stmt ← drawBlockStmt static stack fuel
      match stmt.check? static stack with
      | some next => drawBlock static next fuel count (stmt :: done)
      | none => drawBlock static stack fuel count done

def drawBlockStmt (static : Static) (stack : List Scope) : Nat → Gen Stmt
  | 0 => return .value (.lit 0)
  | fuel + 1 => do
      let factories := callable static stack
      let closures := visibleClosures stack
      match ← drawWeighted [2, 5, if lambdaDepth stack < maximumDepth then 2 else 0,
          if factories.isEmpty then 0 else 1, if closures.isEmpty then 0 else 1] with
      | 0 => return .value (← drawTerm stack 2)
      | 1 => return .assign (← drawTarget stack) (← drawTerm stack 2)
      | 2 => do
          let (body, result) ← drawLambda static stack fuel
          return .lambda body result
      | 3 => return .make (← pick factories) (← drawArgument stack)
      | _ => drawRebind static stack fuel

/-- Rebind a visible closure: to a lambda, another closure or a factory's
closure. -/
def drawRebind (static : Static) (stack : List Scope) : Nat → Gen Stmt
  | 0 => return .value (.lit 0)
  | fuel + 1 => do
      let closures := visibleClosures stack
      let factories := callable static stack
      let (target, _) ← pick closures
      match ← drawWeighted [3, 2, if factories.isEmpty then 0 else 2] with
      | 0 => do
          let (body, result) ← drawLambda static stack fuel
          return .relambda target body result
      | 1 => return .realias target (← pick closures).1
      | _ => return .remake target (← pick factories) (← drawArgument stack)
end

def drawRunStmt (static : Static) (stack : List Scope) (fuel : Nat) : Gen Stmt := do
  let head := stack.head?.getD default
  let factories := callable static stack
  let closures := visibleClosures stack
  let canValue := head.values < maximumValues
  let canClosure := head.closures.length < maximumClosures
  match ← drawWeighted [if canValue then 3 else 0, if canClosure then 5 else 0,
      if canClosure && !closures.isEmpty then 1 else 0, if canClosure && !factories.isEmpty then 5 else 0,
      if factories.isEmpty then 0 else 1, if closures.isEmpty then 0 else 2, 3, 5, 1] with
  | 0 => return .value (← drawTerm stack 2)
  | 1 => do
      let (body, result) ← drawLambda static stack fuel
      return .lambda body result
  | 2 => return .alias (← pick closures).1
  | 3 => return .make (← pick factories) (← drawArgument stack)
  | 4 => return .discard (← pick factories) (← drawArgument stack)
  | 5 => drawRebind static stack fuel
  | 6 => return .assign (← drawTarget stack) (← drawTerm stack 2)
  | 7 => return .observe (← if (← draw 3) == 0 then drawTerm stack 2 else drawCall stack)
  | _ => do
      let count := 2 + (← draw 2)
      let size := 1 + (← draw maximumLoopBody)
      let body ← (List.range size).mapM fun _ => do
        if (← draw 2) == 0 then return Stmt.observe (← drawCall stack)
        else return Stmt.assign (← drawTarget stack) (← drawTerm stack 2)
      return .loop count body

def drawFuel : Nat := 16

/-- `count` statements of `run`, each kept if it checks, and a last observation
of a call when none observes. -/
def drawRun (static : Static) (count : Nat) : Gen (List Stmt × List Scope) := do
  let mut stack : List Scope := [{kind := .run}]
  let mut steps : List Stmt := []
  for _ in List.range count do
    let stmt ← drawRunStmt static stack drawFuel
    if let some next := stmt.check? static stack then
      stack := next
      steps := steps ++ [stmt]
  if !Stmt.listObserves steps then
    let stmt := Stmt.observe (← drawCall stack)
    if let some next := stmt.check? static stack then
      stack := next
      steps := steps ++ [stmt]
  return (steps, stack)

def drawFactory (info : List (Bool × Bool)) (index : Nat) : Gen Factory := do
  let method := (← draw 2) == 0
  let static : Static := {factories := info ++ [(method, false)], within := some index}
  let (body, stack) ← drawBlock static [{kind := .factory method}] drawFuel (← draw (maximumFactorySteps + 1)) []
  let head := stack.head?.getD default
  let returns ← if !head.closures.isEmpty && (← draw 2) == 0 then pure (Returns.closure (← draw head.closures.length))
    else do
      let (body, result) ← drawLambda static stack drawFuel
      pure (Returns.lambda body result)
  let factory : Factory := {method, body, returns}
  if (factory.info? info index).isSome then return factory
  -- Otherwise the factory returns a lambda that sees none of its closures.
  let hidden := stack.modify 0 fun scope => {scope with closures := []}
  let (inner, result) ← drawLambda static hidden drawFuel
  return {factory with returns := .lambda inner result}

def drawCaptures : Gen Plan := do
  let (steps, _) ← drawRun {factories := []} (3 + (← draw (maximumSteps - 3)))
  return {factories := [], steps}

/-- One or two factories, then `run`, which calls one at its end if it called
none. -/
def drawFactories : Gen Plan := do
  let mut factories : List Factory := []
  let mut info : List (Bool × Bool) := []
  for index in List.range (1 + (← draw maximumFactories)) do
    let factory ← drawFactory info index
    if let some entry := factory.info? info index then
      factories := factories ++ [factory]
      info := info ++ [entry]
  let static : Static := {factories := info}
  let (steps, stack) ← drawRun static (3 + (← draw (maximumSteps - 6)))
  if factories.isEmpty || Stmt.listMakes steps then return {factories, steps}
  let index ← draw factories.length
  let argument ← if (info[index]?.map (·.2)).getD false then pure (Term.lit (← pick literals)) else drawArgument stack
  let head := stack.head?.getD default
  if head.closures.length < maximumClosures then
    let closure : Ref := ⟨0, head.closures.length⟩
    let call := Stmt.observe (.call (← drawVia false) closure (← drawTerm stack 1))
    return {factories, steps := steps ++ [.make index argument, call]}
  return {factories, steps := steps ++ [.discard index argument]}

def generateCaptures (seed : UInt64) : Plan := Id.run (drawCaptures.run' {seed, domain := capturesDomain, index := 0})

def generateFactories (seed : UInt64) : Plan :=
  Id.run (drawFactories.run' {seed, domain := factoriesDomain, index := 0})

namespace Plan

/-- Steps are dropped from the end while the reference exceeds the budget and
more than one step remains. -/
def fit (nodes : Nat) (plan : Plan) : Plan := Id.run do
  let mut plan := plan
  for _ in List.range (maximumSteps + 2) do
    if plan.nodes > nodes && plan.steps.length > 1 then plan := {plan with steps := plan.steps.dropLast}
  return plan

end Plan

end Solcore.Synthesis.Core.Captures
end

section
/-! The emitter of the two closure profiles: `run(uint256)` of
`SynthesizedClosureCaptures` or `SynthesizedClosureFactories`. A scope's names
follow its depth: `run` has `sc_x`, `sc_v<k>` and `sc_f<k>`; a factory has
`sc_p` and the same `sc_v<k>` and `sc_f<k>`, so that its names are `run`'s too;
a lambda has `sc_a`, `sc_w<k>` and `sc_g<k>`, and one inside it `sc_b`,
`sc_u<k>` and `sc_h<k>`. The generic helpers `sc_apply` and `sc_twice` and the
field `sc_n` appear when the plan uses them, and a method factory is printed in
the contract. Every local is declared with its value. No emitter proof covers
this text. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Captures
open Solcore.Synthesis.Core.Captures

def capturesEmitterVersion : String := "solcore-source-closure-captures-v2"
def capturesWrapperVersion : String := "solcore-closure-captures-contract-v1"
def capturesContract : String := "SynthesizedClosureCaptures"
def factoriesEmitterVersion : String := "solcore-source-closure-factories-v2"
def factoriesWrapperVersion : String := "solcore-closure-factories-contract-v1"
def factoriesContract : String := "SynthesizedClosureFactories"

def fnText : String := "function (word) returns (word)"

private def indent (count : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate count ' ') ++ line

def paramName (run : Bool) : Nat → String
  | 0 => if run then "sc_x" else "sc_p"
  | 1 => "sc_a"
  | _ => "sc_b"

def valueName (depth index : Nat) : String :=
  (match depth with | 0 => "sc_v" | 1 => "sc_w" | _ => "sc_u") ++ toString index

def closureName (depth index : Nat) : String :=
  (match depth with | 0 => "sc_f" | 1 => "sc_g" | _ => "sc_h") ++ toString index

def opSymbol : Op → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .xor => "^"

def varText (run : Bool) (depth : Nat) : Var → String
  | .param up => paramName run (depth - up)
  | .value ref => valueName (depth - ref.up) ref.index
  | .field => "sc_n"

def refText (depth : Nat) (ref : Ref) : String := closureName (depth - ref.up) ref.index

def termText (run : Bool) (depth : Nat) : Term → String
  | .lit value => toString value
  | .var named => varText run depth named
  | .op op left right => "(" ++ termText run depth left ++ " " ++ opSymbol op ++ " " ++ termText run depth right ++ ")"
  | .checked op left right =>
      "Typedef.rep(uint256(" ++ termText run depth left ++ ") " ++ (if op == .add then "+" else "/") ++ " uint256(" ++
        termText run depth right ++ "))"
  | .call via ref argument =>
      let name := refText depth ref
      let argument := termText run depth argument
      match via with
      | .direct => name ++ "(" ++ argument ++ ")"
      | .apply => "sc_apply(" ++ name ++ ", " ++ argument ++ ")"
      | .twice => "sc_twice(" ++ name ++ ", " ++ argument ++ ")"

def makeText (run : Bool) (depth factory : Nat) (argument : Term) : String :=
  "sc_mk" ++ toString factory ++ "(" ++ termText run depth argument ++ ")"

/-- A lambda after `lead`, around its body's lines. -/
def lambdaWrap (run : Bool) (depth : Nat) (lead : String) (inner : List String) (result : Term) : List String :=
  [lead ++ "lam (" ++ paramName run (depth + 1) ++ ": word) -> word {"] ++
    indent 4 (inner ++ ["return " ++ termText run (depth + 1) result ++ ";"]) ++ ["};"]

/-- How many names a block has declared: Word locals, closures and loops. -/
structure Counts where
  values : Nat := 0
  closures : Nat := 0
  loops : Nat := 0

mutual
def blockLines (run : Bool) (depth : Nat) (counts : Counts) : List Stmt → List String × Counts
  | [] => ([], counts)
  | stmt :: rest =>
      let (lines, counts) := stmtLines run depth counts stmt
      let (more, counts) := blockLines run depth counts rest
      (lines ++ more, counts)

def stmtLines (run : Bool) (depth : Nat) (counts : Counts) : Stmt → List String × Counts
  | .value init => (["let " ++ valueName depth counts.values ++ ": word = " ++ termText run depth init ++ ";"],
      {counts with values := counts.values + 1})
  | .assign target assigned => ([varText run depth target ++ " = " ++ termText run depth assigned ++ ";"], counts)
  | .lambda body result =>
      (lambdaWrap run depth ("let " ++ closureName depth counts.closures ++ ": " ++ fnText ++ " = ")
        (blockLines run (depth + 1) {} body).1 result, {counts with closures := counts.closures + 1})
  | .alias source =>
      (["let " ++ closureName depth counts.closures ++ ": " ++ fnText ++ " = " ++ refText depth source ++ ";"],
        {counts with closures := counts.closures + 1})
  | .make factory argument =>
      (["let " ++ closureName depth counts.closures ++ ": " ++ fnText ++ " = " ++ makeText run depth factory argument ++
        ";"], {counts with closures := counts.closures + 1})
  | .discard factory argument => ([makeText run depth factory argument ++ ";"], counts)
  | .relambda target body result =>
      (lambdaWrap run depth (refText depth target ++ " = ") (blockLines run (depth + 1) {} body).1 result, counts)
  | .realias target source => ([refText depth target ++ " = " ++ refText depth source ++ ";"], counts)
  | .remake target factory argument =>
      ([refText depth target ++ " = " ++ makeText run depth factory argument ++ ";"], counts)
  | .observe observed => (["sc_r = ((sc_r * 1099511628211) ^ " ++ termText run depth observed ++ ");"], counts)
  | .loop count body =>
      let counter := "sc_i" ++ toString counts.loops
      let inner := (blockLines run depth {counts with loops := counts.loops + 1} body).1
      (["let " ++ counter ++ ": word = 0;", "while (" ++ counter ++ " < " ++ toString count ++ ") {"] ++
        indent 4 (inner ++ [counter ++ " = " ++ counter ++ " + 1;"]) ++ ["}"], {counts with loops := counts.loops + 1})
end

def factoryLines (index : Nat) (factory : Factory) : List String :=
  let inner := (blockLines false 0 {} factory.body).1
  let returns := match factory.returns with
    | .closure closure => ["return " ++ closureName 0 closure ++ ";"]
    | .lambda body result => lambdaWrap false 0 "return " (blockLines false 1 {} body).1 result
  ["function sc_mk" ++ toString index ++ "(sc_p: word) returns (" ++ fnText ++ ") {"] ++ indent 4 (inner ++ returns) ++
    ["}"]

def helperLines (plan : Plan) : List String :=
  (if plan.usesVia .apply then
    ["function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {", "    return f(x);", "}", ""] else []) ++
  (if plan.usesVia .twice then
    ["function sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {", "    return f(f(x));", "}", ""] else [])

def emitWith (contract : String) (plan : Plan) : EmittedProgram :=
  let factories := plan.factories.zipIdx.map fun (factory, index) => (factory.method, factoryLines index factory)
  let free := (factories.filter (!·.1)).flatMap fun (_, lines) => lines ++ [""]
  let methods := (factories.filter (·.1)).flatMap fun (_, lines) => indent 4 lines ++ [""]
  let field := if plan.usesField then ["    sc_n: word;", ""] else []
  let body := ["let sc_x: word = Typedef.rep(input);", "let sc_r: word = 0;"] ++ (blockLines true 0 {} plan.steps).1 ++
    ["return uint256(sc_r);"]
  let lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;", ""] ++ helperLines plan ++ free ++
    ["contract " ++ contract ++ " {"] ++ field ++ methods ++
    ["    function run(input: uint256) public returns (uint256) {"] ++ indent 8 body ++ ["    }", "}"]
  { source := String.intercalate "\n" lines ++ "\n", contractName := contract, methodName := "run",
    methodSignature := "run(uint256)", deployPath := [contract ++ "Deploy"],
    runtimePath := [contract ++ "Deploy", contract] }

def emitCaptures (plan : Plan) : EmittedProgram := emitWith capturesContract plan

def emitFactories (plan : Plan) : EmittedProgram := emitWith factoriesContract plan

end Solcore.Synthesis.Source.Captures
end

section
/-! Reductions of closure plans. A reduction keeps every declaration, so that
the indices of later locals and closures stay valid: it removes a statement that
declares nothing, empties a lambda, shortens a loop or replaces a term by `0` or
by one of its parts. Admission and the full Core checker decide again. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Captures

def Term.size : Term → Nat
  | .lit _ | .var _ => 1
  | .op _ left right | .checked _ left right => 1 + left.size + right.size
  | .call _ _ argument => 2 + argument.size

def Stmt.size : Stmt → Nat
  | .value term | .assign _ term | .observe term => 1 + term.size
  | .lambda body result | .relambda _ body result => 2 + (body.map Stmt.size).sum + result.size
  | .alias _ | .realias .. => 1
  | .make _ term | .discard _ term | .remake _ _ term => 2 + term.size
  | .loop count body => count + (body.map Stmt.size).sum

def Returns.size : Returns → Nat
  | .closure _ => 1
  | .lambda body result => 2 + (body.map Stmt.size).sum + result.size

def Plan.size (plan : Plan) : Nat :=
  (plan.steps.map Stmt.size).sum + (plan.factories.map fun factory =>
    1 + (factory.body.map Stmt.size).sum + factory.returns.size).sum

def Stmt.declares : Stmt → Bool
  | .value _ | .lambda .. | .alias _ | .make .. => true
  | _ => false

def Term.smaller : Term → List Term
  | .lit value => if value = 0 then [] else [.lit 0]
  | .var _ => [.lit 0]
  | .op operation left right =>
      [.lit 0, left, right] ++ left.smaller.map (.op operation · right) ++ right.smaller.map (.op operation left ·)
  | .checked operation left right =>
      [.lit 0, left, right] ++ left.smaller.map (.checked operation · right) ++
        right.smaller.map (.checked operation left ·)
  | .call via ref argument =>
      [.lit 0, argument] ++ (if via == .direct then [] else [.call .direct ref argument]) ++
        argument.smaller.map (.call via ref ·)

mutual
def Stmt.smaller : Stmt → List Stmt
  | .value init => init.smaller.map .value
  | .assign target assigned => assigned.smaller.map (.assign target)
  | .lambda body result =>
      .lambda [] (.lit 0) :: ((Stmt.listSmaller body).map (.lambda · result) ++ result.smaller.map (.lambda body ·))
  | .alias _ | .realias .. => []
  | .make factory argument => argument.smaller.map (.make factory)
  | .discard factory argument => argument.smaller.map (.discard factory)
  | .relambda target body result =>
      .relambda target [] (.lit 0) ::
        ((Stmt.listSmaller body).map (.relambda target · result) ++ result.smaller.map (.relambda target body ·))
  | .remake target factory argument => argument.smaller.map (.remake target factory)
  | .observe observed => observed.smaller.map .observe
  | .loop count body =>
      (if count > 1 then [.loop (count - 1) body] else []) ++ (Stmt.listSmaller body).map (.loop count ·)

/-- Remove one statement that declares nothing, or reduce one statement. -/
def Stmt.listSmaller : List Stmt → List (List Stmt)
  | [] => []
  | stmt :: rest =>
      (if stmt.declares then [] else [rest]) ++ stmt.smaller.map (· :: rest) ++
        (Stmt.listSmaller rest).map (stmt :: ·)
end

def Returns.smaller : Returns → List Returns
  | .closure _ => []
  | .lambda body result =>
      .lambda [] (.lit 0) :: ((Stmt.listSmaller body).map (.lambda · result) ++ result.smaller.map (.lambda body ·))

namespace Plan

/-- Every one-step reduction of `run`, of a factory's body or of what a
factory returns. -/
def reductions (plan : Plan) : List Plan :=
  (Stmt.listSmaller plan.steps).map ({plan with steps := ·}) ++
  plan.factories.zipIdx.flatMap fun (factory, index) =>
    ((Stmt.listSmaller factory.body).map fun body => {factory with body}) ++
      (factory.returns.smaller.map fun returns => {factory with returns}) |>.map fun factory =>
        {plan with factories := plan.factories.set index factory}

end Plan

end Solcore.Synthesis.Core.Captures
end

section
/-! The cases of the two closure profiles, `runtime-closure-captures` and
`runtime-closure-factories`. A case retains its plan, drawn from the case seed,
and the plan's complete original Core reference at the case input, built from
the plan, never from the source. The reference's left injection is the fold,
its right injection the revert data of a checked operation, a length and two
Words, observed as the bytes they hold. Saved observations never supply the
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Captures
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Captures

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

/-- The node budget, which bounds the applied reference, and the decode bound of
a saved reference. -/
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

/-! Plan JSON. Decoding is strict and the decoded plan must re-encode to the
saved JSON. -/

def opName : Op → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .xor => "xor"

def viaName : Via → String
  | .direct => "direct"
  | .apply => "apply"
  | .twice => "twice"

def refJson (ref : Ref) : Json := Json.arr #[toJson ref.up, toJson ref.index]

def varJson : Var → Json
  | .param up => Json.mkObj [("param", toJson up)]
  | .value ref => Json.mkObj [("value", refJson ref)]
  | .field => toJson "field"

def termJson : Captures.Term → Json
  | .lit value => Json.mkObj [("lit", toJson (toString value))]
  | .var named => Json.mkObj [("var", varJson named)]
  | .op op left right => Json.mkObj [("op", toJson (opName op)), ("left", termJson left), ("right", termJson right)]
  | .checked op left right => Json.mkObj [("checked", toJson (if op == .add then "add" else "div")),
      ("left", termJson left), ("right", termJson right)]
  | .call via ref argument => Json.mkObj [("call", toJson (viaName via)), ("closure", refJson ref),
      ("argument", termJson argument)]

def stmtJson : Stmt → Json
  | .value init => Json.mkObj [("value", termJson init)]
  | .assign target assigned => Json.mkObj [("assign", varJson target), ("term", termJson assigned)]
  | .lambda body result => Json.mkObj [("lambda", Json.arr (body.map stmtJson).toArray), ("result", termJson result)]
  | .alias source => Json.mkObj [("alias", refJson source)]
  | .make factory argument => Json.mkObj [("make", toJson factory), ("argument", termJson argument)]
  | .discard factory argument => Json.mkObj [("discard", toJson factory), ("argument", termJson argument)]
  | .relambda target body result => Json.mkObj [("relambda", refJson target),
      ("body", Json.arr (body.map stmtJson).toArray), ("result", termJson result)]
  | .realias target source => Json.mkObj [("realias", refJson target), ("source", refJson source)]
  | .remake target factory argument => Json.mkObj [("remake", refJson target), ("factory", toJson factory),
      ("argument", termJson argument)]
  | .observe observed => Json.mkObj [("observe", termJson observed)]
  | .loop count body => Json.mkObj [("loop", toJson count), ("body", Json.arr (body.map stmtJson).toArray)]

def returnsJson : Returns → Json
  | .closure index => Json.mkObj [("closure", toJson index)]
  | .lambda body result => Json.mkObj [("lambda", Json.arr (body.map stmtJson).toArray), ("result", termJson result)]

def factoryJson (factory : Factory) : Json := Json.mkObj [("method", toJson factory.method),
  ("body", Json.arr (factory.body.map stmtJson).toArray), ("returns", returnsJson factory.returns)]

def planJsonWith (schema : String) (plan : Plan) : Json := Json.mkObj [
  ("schema", toJson schema), ("factories", Json.arr (plan.factories.map factoryJson).toArray),
  ("steps", Json.arr (plan.steps.map stmtJson).toArray)]

private def natText (text : String) : Except String Nat :=
  match text.toNat? with
  | some value => if toString value == text then .ok value else .error "noncanonical closure plan number"
  | none => .error "closure plan number is not decimal"

private def list (json : Json) : Except String (List Json) := do return (← json.getArr?).toList

def refOf (json : Json) : Except String Ref := do
  match ← list json with
  | [up, index] => return ⟨← up.getNat?, ← index.getNat?⟩
  | _ => throw "closure plan reference is not a pair"

def varOf (json : Json) : Except String Var := do
  if json == toJson "field" then return .field
  if let .ok up := json.getObjValAs? Nat "param" then return .param up
  return .value (← refOf (← json.getObjVal? "value"))

def opOf : String → Except String Op
  | "add" => .ok .add
  | "sub" => .ok .sub
  | "mul" => .ok .mul
  | "xor" => .ok .xor
  | _ => .error "unknown closure plan operation"

def viaOf : String → Except String Via
  | "direct" => .ok .direct
  | "apply" => .ok .apply
  | "twice" => .ok .twice
  | _ => .error "unknown closure call"

/-- Decoders take a depth bound: a saved plan nests at most a few levels. -/
def decodeDepth : Nat := 64

def termOf : Nat → Json → Except String Captures.Term
  | 0, _ => .error "closure plan term nests too deeply"
  | fuel + 1, json => do
      if let .ok text := json.getObjValAs? String "lit" then return .lit (← natText text)
      if let .ok named := json.getObjVal? "var" then return .var (← varOf named)
      if let .ok text := json.getObjValAs? String "op" then
        return .op (← opOf text) (← termOf fuel (← json.getObjVal? "left")) (← termOf fuel (← json.getObjVal? "right"))
      if let .ok text := json.getObjValAs? String "checked" then
        let op ← match text with
          | "add" => pure Checked.add
          | "div" => pure Checked.div
          | _ => throw "unknown checked operation"
        return .checked op (← termOf fuel (← json.getObjVal? "left")) (← termOf fuel (← json.getObjVal? "right"))
      if let .ok text := json.getObjValAs? String "call" then
        return .call (← viaOf text) (← refOf (← json.getObjVal? "closure")) (← termOf fuel (← json.getObjVal? "argument"))
      throw "unknown closure plan term"

def stmtOf : Nat → Json → Except String Stmt
  | 0, _ => .error "closure plan statement nests too deeply"
  | fuel + 1, json => do
      let stmts (key : String) : Except String (List Stmt) := do (← list (← json.getObjVal? key)).mapM (stmtOf fuel)
      let term (key : String) : Except String Captures.Term := do termOf decodeDepth (← json.getObjVal? key)
      if let .ok init := json.getObjVal? "value" then return .value (← termOf decodeDepth init)
      if let .ok target := json.getObjVal? "assign" then return .assign (← varOf target) (← term "term")
      if (json.getObjVal? "lambda").isOk then return .lambda (← stmts "lambda") (← term "result")
      if let .ok source := json.getObjVal? "alias" then return .alias (← refOf source)
      if let .ok factory := json.getObjValAs? Nat "make" then return .make factory (← term "argument")
      if let .ok factory := json.getObjValAs? Nat "discard" then return .discard factory (← term "argument")
      if let .ok target := json.getObjVal? "relambda" then
        return .relambda (← refOf target) (← stmts "body") (← term "result")
      if let .ok target := json.getObjVal? "realias" then
        return .realias (← refOf target) (← refOf (← json.getObjVal? "source"))
      if let .ok target := json.getObjVal? "remake" then
        return .remake (← refOf target) (← json.getObjValAs? Nat "factory") (← term "argument")
      if let .ok observed := json.getObjVal? "observe" then return .observe (← termOf decodeDepth observed)
      if let .ok count := json.getObjValAs? Nat "loop" then return .loop count (← stmts "body")
      throw "unknown closure plan statement"

def returnsOf (json : Json) : Except String Returns := do
  if let .ok index := json.getObjValAs? Nat "closure" then return .closure index
  return .lambda (← (← list (← json.getObjVal? "lambda")).mapM (stmtOf decodeDepth))
    (← termOf decodeDepth (← json.getObjVal? "result"))

def factoryOf (json : Json) : Except String Factory := do
  let method ← json.getObjValAs? Bool "method"
  let body ← (← list (← json.getObjVal? "body")).mapM (stmtOf decodeDepth)
  let returns ← returnsOf (← json.getObjVal? "returns")
  return {method, body, returns}

def planOfWith (schema : String) (json : Json) : Except String Plan := do
  unless (← json.getObjValAs? String "schema") = schema do throw "unsupported closure plan schema"
  let factories ← (← list (← json.getObjVal? "factories")).mapM factoryOf
  let steps ← (← list (← json.getObjVal? "steps")).mapM (stmtOf decodeDepth)
  return {factories, steps}

namespace Profile

def planJson (profile : Profile) (plan : Plan) : Json := planJsonWith profile.planSchema plan

def checkedPlan (profile : Profile) (json : Json) : Except String (CheckedPlan profile) := do
  let plan ← planOfWith profile.planSchema json
  unless profile.admitted plan do
    throw (profile.label ++ " plan is outside the admitted scopes, statements and calls")
  let some checked := CheckedPlan.ofPlan? (profile := profile) plan
    | throw (profile.label ++ " reference failed the full Core checker")
  unless json == profile.planJson plan do
    throw ("saved " ++ profile.label ++ " plan differs from its canonical checked representation")
  unless plan.nodes ≤ caseLimit do throw (profile.label ++ " reference exceeds the 4,096-node case limit")
  return checked

def shapesJson (profile : Profile) (plan : Plan) : Json :=
  Json.mkObj ((profile.shapes plan).map fun (dimension, values) => (dimension, toJson values))

end Profile

/-! Observation: the left injection is the fold, the right injection the revert
data. -/

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

def hexBytes (bytes : List Nat) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

def wordBytes (value : Nat) : List Nat := (List.range 32).reverse.map fun index => (value / 256 ^ index) % 256

/-- A returned Word or revert data. -/
inductive Observed where
  | word (value : Word)
  | reverted (data : List Nat)
  deriving BEq

def Observed.ofValue? : Solcore.Core.Value → Option Observed
  | .inLeft _ (.word returned) => some (.word returned)
  | .inRight _ (.pair (.word length) (.pair (.word first) (.word second))) =>
      if length.val ≤ 64 then some (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val)) else none
  | _ => none

def observe {profile : Profile} (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.program input).toCore.runStateful fuel with
    | .done value _ => match Observed.ofValue? value with
        | some (.word word) => [("status", toJson "returned"), ("word", toJson (toString word.val))]
        | some (.reverted data) => [("status", toJson "reverted"), ("output", toJson (hexBytes data))]
        | none => [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

namespace Profile

def makeCase (profile : Profile) (plan : CheckedPlan profile) (input : Word) (emitted : EmittedProgram) (origin : Json)
    (fuel : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson profile.caseSchema), (profile.planKey, profile.planJson plan.plan),
    ("program", Wire.encodeProgram (plan.program input)),
    ("input", toJson (toString input.val)), ("source", toJson emitted.source),
    ("provenance", Json.mkObj [
      ("origin", origin), ("profileVersion", toJson profile.profileVersion),
      ("generatorVersion", toJson Captures.version), ("boundaryVersion", toJson Primitive.boundaryVersion),
      ("emitterVersion", toJson profile.emitterVersion), ("wrapperVersion", toJson profile.wrapperVersion),
      ("features", toJson ([] : List String)), ("referenceNodes", toJson plan.plan.nodes),
      (profile.shapesKey, profile.shapesJson plan.plan)]),
    ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
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
    | .reverted _ => none
  if words.length = outcomes.length then acceptance.check Primitive.boundaryInputs words

/-- The seed's plan, its steps dropped from the end while the reference exceeds
the budget. -/
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
      ("profileVersion", profile.profileVersion), ("generatorVersion", Captures.version),
      ("boundaryVersion", Primitive.boundaryVersion),
      ("emitterVersion", profile.emitterVersion), ("wrapperVersion", profile.wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do
      throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted := profile.emit admitted.plan.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw ("saved source differs from emission of the " ++ profile.label ++ " plan")
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
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

end Solcore.Synthesis.Source.Captures
end

section
/-! A `runtime-closure-captures` case: Word locals and closures of one `run`
body, with writes through captures, repeated calls, rebinding and the field, at
an input that `run(uint256)` receives. Its reference panics with `Panic(0x11)`
or `Panic(0x12)`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ClosureCaptures
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Captures
open Solcore.Synthesis.Source.Captures (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-closure-captures-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.closure-captures-plan.v1",
  profileVersion := "runtime-closure-captures-v1/plan-seed-v1",
  emitterVersion := Captures.capturesEmitterVersion, wrapperVersion := Captures.capturesWrapperVersion,
  planKey := "closureCapturesPlan", shapesKey := "closureCapturesShapes",
  originKind := "closure-captures-generated", stage := "closure-captures-profile", label := "closure captures",
  admitted := Plan.capturesAdmitted, generate := generateCaptures, emit := Captures.emitCaptures,
  shapes := Plan.capturesShapes, minimumNodes := 256 }

def maximumNodes : Nat := Captures.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Captures.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.ClosureCaptures
end

section
/-! A `runtime-closure-factories` case: one or two factories, free functions or
contract methods, that return closures over their parameter and locals, called
from `run` or its lambdas with the factory locals' names reused in `run`, with
their effects on the field and their checked operations. Its reference panics
with `Panic(0x11)` or `Panic(0x12)`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ClosureFactories
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Captures
open Solcore.Synthesis.Source.Captures (Profile CheckedPlan CheckedInput)

def caseSchema : String := "solcore-lean.semantic-closure-factories-case.v1"

def profile : Profile := {
  caseSchema, planSchema := "solcore-lean.closure-factories-plan.v1",
  profileVersion := "runtime-closure-factories-v1/plan-seed-v1",
  emitterVersion := Captures.factoriesEmitterVersion, wrapperVersion := Captures.factoriesWrapperVersion,
  planKey := "closureFactoriesPlan", shapesKey := "closureFactoriesShapes",
  originKind := "closure-factories-generated", stage := "closure-factories-profile", label := "closure factories",
  admitted := Plan.factoriesAdmitted, generate := generateFactories, emit := Captures.emitFactories,
  shapes := Plan.factoriesShapes, minimumNodes := 256 }

def maximumNodes : Nat := Captures.maximumNodes

def checkedPlan (json : Json) : Except String (CheckedPlan profile) := profile.checkedPlan json

def caseProgram (json : Json) : Except String (CheckedInput profile) := profile.caseProgram json

def observe (plan : CheckedPlan profile) (input : Word) (fuel : Nat) : Json := Captures.observe plan input fuel

def emitCase (plan : CheckedPlan profile) (input : Word) (origin : Json) (fuel : Nat) : Except String Json :=
  profile.emitCase plan input origin fuel

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (inputSelection : InputSelection := .boundary) (acceptance : Acceptance := .profile) : Json :=
  profile.generateCases firstSeed nodes count attempts fuel inputSelection acceptance

def replayCase (json : Json) (fuel : Nat) : Except String Json := profile.replayCase json fuel

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := profile.shrinkCases json limit fuel

end Solcore.Synthesis.Source.ClosureFactories
end
