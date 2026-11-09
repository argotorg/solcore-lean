import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec
import Solcore.Synthesis.Internal.CallGraphs
import Solcore.Synthesis.Internal.Functions

/-!
# Profiles: loops and recursion

The profiles `runtime-loops`, `runtime-nested-loops`, `runtime-call-graph-loops`,
`runtime-loop-closures`, `runtime-recursion` and `runtime-recursive-loops`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.BoundedLoop
/-! Bounded loops have an independent, finite Core reference. The source loop
uses a mutable counter; this Core expression instead checks each literal ordinal
against an immutable bound. The complete helper DAG and arbitrary entry closure
are evaluated once before the input is supplied. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.BoundedLoop

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-bounded-loop-plan-v1"

def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The preceding ordinal guards each introduce one Unit binder. At ordinal
`i`, the accumulator, bound, input and entry closure therefore occupy indices
`i`, `i + 1`, `i + 2` and `i + 3`. There is no Core counter cell. -/
private def guards : Nat → Nat → Expr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1)) (.word (Word.ofNatModulo ordinal)))
        (.storeCell (.var ordinal)
          (.apply (.var (ordinal + 3)) (.loadCell (.var ordinal)))) .unit)
        (guards remaining (ordinal + 1))

private def loopExpression (stepBody : Expr) (mask : Nat) : Expr :=
  .letE stepBody (.lambda .word .word
    (.letE (.binary .wordAnd (.var 0) (.word (Word.ofNatModulo mask)))
      (.letE (.newCell .word (.var 1)) (guards mask 0))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask : Nat) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := loopExpression step.program.body mask
}

def appliedProgram (step : Aggregates.CheckedDAG) (mask : Nat) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step mask).body (.word input)
}

def canonicalNodes (step : Aggregates.CheckedDAG) (mask : Nat) : Nat :=
  programNodes (canonicalProgram step mask)

def appliedNodes (step : Aggregates.CheckedDAG) (mask : Nat) : Nat :=
  programNodes (appliedProgram step mask Word.zero)

/-- Measure the actual wrapper syntax using a one-node placeholder. It is only
a size calculation, not a checked or executable placeholder program. Cases use
this overhead before generating the step DAG and remeasure the complete result. -/
def appliedOverhead (mask : Nat) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (loopExpression (.word Word.zero) mask) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  allowed : AllowedMask mask
  checked : (canonicalProgram step mask).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask

def ofParts? (step : Aggregates.CheckedDAG) (mask : Nat) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if checked : (canonicalProgram step mask).check = true then
      some ⟨step, mask, allowed, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.mask input

theorem instantiate_wellTyped (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).WellTyped := by
  refine ⟨plan.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, appliedProgram, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply plan.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  Program.check_complete (plan.instantiate_wellTyped input)

end CheckedPlan
end Solcore.Synthesis.Core.BoundedLoop
end

section
-- leanmerge: from Solcore.Synthesis.Core.CallGraphLoop
/-! Bounded loops whose step is a directly generated scalar call graph. The
unchanged helpers and entry are resealed by the aggregate DAG checker, then by
the existing bounded-loop plan. Its finite ordinal guards remain the only Core
reference; this module adds no evaluator and no Core primitive. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallGraphLoop

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-call-graph-loop-plan-v1"
def grammarVersion : String := "core-call-graph-loop-grammar-v1/" ++ CallGraph.version

/-- The executed loop step is the scalar graph's exact declaration chain. -/
structure CheckedPlan where private mk ::
  graph : CheckedWordFunctionDAG
  loop : BoundedLoop.CheckedPlan
  sameHelpers : loop.step.helpers = graph.helpers
  sameEntry : loop.step.entry = graph.entry

namespace CheckedPlan

def mask (plan : CheckedPlan) : Nat := plan.loop.mask

def program (plan : CheckedPlan) : Program := plan.loop.program

def instantiate (plan : CheckedPlan) (input : Word) : Program := plan.loop.instantiate input

def features (plan : CheckedPlan) : List String := plan.graph.features

/-- Seal only a scalar graph whose unchanged parts pass both the aggregate
DAG checker and the full Core check of the canonical bounded loop. -/
def ofParts? (graph : CheckedWordFunctionDAG) (mask : Nat) : Option CheckedPlan := do
  let step ← Aggregates.CheckedDAG.ofParts? graph.helpers graph.entry
  let loop ← BoundedLoop.CheckedPlan.ofParts? step mask
  if same : loop.step.helpers = graph.helpers ∧ loop.step.entry = graph.entry then
    some ⟨graph, loop, same.1, same.2⟩
  else none

/-- Saved plans name the scalar graph program; any other step is rejected. -/
def ofProgram? (step : Program) (mask : Nat) : Option CheckedPlan := do
  ofParts? (← CheckedWordFunctionDAG.ofProgram? step) mask

theorem step_program (plan : CheckedPlan) : plan.loop.step.program = plan.graph.program := by
  simp only [Aggregates.CheckedDAG.program, CheckedWordFunctionDAG.program,
    plan.sameHelpers, plan.sameEntry]

theorem program_eq (plan : CheckedPlan) :
    plan.program = BoundedLoop.canonicalProgram plan.loop.step plan.mask := rfl

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.loop.check

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped := plan.loop.wellTyped

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  plan.loop.instantiate_checked input

end CheckedPlan

structure Request where
  seed : Seed
  maxProgramNodes : Nat
  deriving Repr, BEq, DecidableEq

inductive Error where
  | budgetTooSmall
  | budgetTooLarge
  | step (error : CallGraph.Error)
  | checkerInvariant
  | budgetInvariant
  deriving Repr, BEq, DecidableEq

def generatedMasks : List Nat := [1, 3, 7]

/-- The step is measured after subtracting the existing loop-wrapper overhead. -/
def minimumAppliedNodes (mask : Nat) : Nat :=
  BoundedLoop.appliedOverhead mask + CallGraph.minimumAppliedNodes 1

structure Generated where private mk ::
  initialSeed : Seed
  maxProgramNodes : Nat
  stepBudget : Nat
  step : CallGraph.Generated
  plan : CheckedPlan
  sameGraph : plan.graph.helpers = step.function.helpers ∧ plan.graph.entry = step.function.entry
  bounded : programNodes (plan.instantiate Word.zero) ≤ maxProgramNodes

namespace Generated

def finalSeed (generated : Generated) : Seed := generated.step.finalSeed

def nodeCount (generated : Generated) : Nat := programNodes (generated.plan.instantiate Word.zero)

end Generated

/-- Scale the upper half of one draw to the mask list. A remainder of those bits
cycles poorly over consecutive campaign seeds. The scalar generator starts from
the following state, so mask and helper count use different draws. -/
def generate (request : Request) : Except Error Generated := do
  if request.maxProgramNodes > 512 then throw .budgetTooLarge
  let (value, stepSeed) := request.seed.draw
  let mask := generatedMasks[(value.toNat / 2 ^ 32) * generatedMasks.length / 2 ^ 32]?.getD 1
  let overhead := BoundedLoop.appliedOverhead mask
  if request.maxProgramNodes < minimumAppliedNodes mask then throw .budgetTooSmall
  let stepBudget := request.maxProgramNodes - overhead
  let step ← (CallGraph.generate {seed := stepSeed, maxProgramNodes := stepBudget}).mapError .step
  let some plan := CheckedPlan.ofParts? step.function mask | throw .checkerInvariant
  if same : plan.graph.helpers = step.function.helpers ∧ plan.graph.entry = step.function.entry then
    if bounded : programNodes (plan.instantiate Word.zero) ≤ request.maxProgramNodes then
      return ⟨request.seed, request.maxProgramNodes, stepBudget, step, plan, same, bounded⟩
    else throw .budgetInvariant
  else throw .checkerInvariant

end Solcore.Synthesis.Core.CallGraphLoop
end

section
-- leanmerge: from Solcore.Synthesis.Core.LoopClosure
/-! Closures created in bounded loop bodies have an independent, finite Core
reference. The source loop uses a mutable counter and creates a fresh closure
in every iteration; this Core expression instead checks each literal ordinal
against an immutable bound, as for bounded loops, and every run guard builds
a Core lambda over an immutable Word snapshot. The complete step DAG is
evaluated once before the input is supplied. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.LoopClosure

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-loop-closure-plan-v1"

/-- A loop with mask `m` runs at most `m` iterations. -/
def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The loop-carried Word local each iteration's closure captures. -/
inductive Capture where
  /-- `f(a) = step(acc + a)`, then `acc = acc + 1` and `acc = f(c) + acc`. -/
  | accumulator
  /-- `f(a) = step(a) + c`, then `c = c + 1` and `acc = sc_apply(f, acc)`. -/
  | counter
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Capture

def all : List Capture := [.accumulator, .counter]

def name : Capture → String
  | .accumulator => "accumulator"
  | .counter => "counter"

def ofString? : String → Option Capture
  | "accumulator" => some .accumulator
  | "counter" => some .counter
  | _ => none

end Capture

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def wordFunction : Ty := .function .word .word

/-- The source's generic higher-order apply function, instantiated at Word. -/
private def applyFunction : Expr :=
  .lambda wordFunction wordFunction (.lambda .word .word (.apply (.var 1) (.var 0)))

/-- The iteration of ordinal `i`, after its `i` Unit binders, where the
accumulator cell, bound, input, apply function and step closure occupy indices
`i` to `i + 4`. The snapshot is bound first and the closure next; inside the
lambda, index zero is the argument and index one the snapshot. -/
private def iteration (capture : Capture) (ordinal : Nat) : Expr :=
  match capture with
  | .accumulator =>
      .letE (.loadCell (.var ordinal))
        (.letE (.lambda .word .word (.apply (.var (ordinal + 6)) (.binary .wordAdd (.var 1) (.var 0))))
          (.letE (.storeCell (.var (ordinal + 2)) (.binary .wordAdd (.loadCell (.var (ordinal + 2))) (word 1)))
            (.storeCell (.var (ordinal + 3))
              (.binary .wordAdd (.apply (.var 1) (word ordinal)) (.loadCell (.var (ordinal + 3)))))))
  | .counter =>
      .letE (word ordinal)
        (.letE (.lambda .word .word (.binary .wordAdd (.apply (.var (ordinal + 6)) (.var 0)) (.var 1)))
          (.storeCell (.var (ordinal + 2)) (.apply (.apply (.var (ordinal + 5)) (.var 0)) (.loadCell (.var (ordinal + 2))))))

private def guards (capture : Capture) : Nat → Nat → Expr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1)) (word ordinal)) (iteration capture ordinal) .unit)
        (guards capture remaining (ordinal + 1))

private def loopExpression (stepBody : Expr) (mask : Nat) (capture : Capture) : Expr :=
  .letE stepBody (.letE applyFunction (.lambda .word .word
    (.letE (.binary .wordAnd (.var 0) (word mask))
      (.letE (.newCell .word (.var 1)) (guards capture mask 0)))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask : Nat) (capture : Capture) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := loopExpression step.program.body mask capture
}

def appliedProgram (step : Aggregates.CheckedDAG) (mask : Nat) (capture : Capture) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step mask capture).body (.word input)
}

/-- Measure the actual wrapper syntax with a one-node placeholder step. It is
only a size calculation; cases remeasure the complete program after generating
the step DAG. -/
def appliedOverhead (mask : Nat) (capture : Capture) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (loopExpression (.word Word.zero) mask capture) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  capture : Capture
  allowed : AllowedMask mask
  checked : (canonicalProgram step mask capture).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask plan.capture

def ofParts? (step : Aggregates.CheckedDAG) (mask : Nat) (capture : Capture) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if checked : (canonicalProgram step mask capture).check = true then
      some ⟨step, mask, capture, allowed, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.mask plan.capture input

theorem instantiate_wellTyped (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).WellTyped := by
  refine ⟨plan.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, appliedProgram, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply plan.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  Program.check_complete (plan.instantiate_wellTyped input)

/-- The iterations a call runs. -/
def iterations (plan : CheckedPlan) (input : Word) : Nat :=
  (input.bitAnd (Word.ofNatModulo plan.mask)).val

end CheckedPlan
end Solcore.Synthesis.Core.LoopClosure
end

section
-- leanmerge: from Solcore.Synthesis.Core.NestedLoop
/-! Nested bounded loops have an independent, finite Core reference. The source
runs an outer and an inner while loop with mutable counters; this Core
expression instead checks literal outer and inner ordinals against immutable
bounds over one accumulator cell, with no counter cell. The complete step DAG
is evaluated once before the input is supplied. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.NestedLoop

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-nested-loop-plan-v1"

/-- A loop with mask `m` runs at most `m` iterations. -/
def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3))

/-- What the inner bound of every outer iteration reads. -/
inductive Bound where
  /-- The input, the same in every outer iteration. -/
  | input
  /-- The outer counter plus one. -/
  | counter
  /-- The accumulator the previous outer iterations computed. -/
  | accumulator
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Bound

def all : List Bound := [.input, .counter, .accumulator]

def name : Bound → String
  | .input => "input"
  | .counter => "counter"
  | .accumulator => "accumulator"

def ofString? : String → Option Bound
  | "input" => some .input
  | "counter" => some .counter
  | "accumulator" => some .accumulator
  | _ => none

end Bound

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- At outer ordinal `a`, after its `a` Unit binders, the accumulator cell,
outer bound, input and step closure occupy indices `a`, `a + 1`, `a + 2` and
`a + 3`. The counter bound is the source counter plus one. -/
private def innerBound (bound : Bound) (inner ordinal : Nat) : Expr :=
  match bound with
  | .input => .binary .wordAnd (.var (ordinal + 2)) (word inner)
  | .counter => .binary .wordAnd (.binary .wordAdd (word ordinal) (word 1)) (word inner)
  | .accumulator => .binary .wordAnd (.loadCell (.var ordinal)) (word inner)

/-- Inside outer ordinal `outer`, after the inner bound and `b` Unit binders,
the inner bound is index `b`, the accumulator `outer + 1 + b` and the step
closure three further out. -/
private def innerGuards (outer : Nat) : Nat → Nat → Expr
  | 0, _ => .unit
  | remaining + 1, ordinal =>
      let accumulator := outer + 1 + ordinal
      .letE (.ifE (.binary .wordGt (.var ordinal) (word ordinal))
          (.storeCell (.var accumulator)
            (.apply (.var (accumulator + 3)) (.loadCell (.var accumulator)))) .unit)
        (innerGuards outer remaining (ordinal + 1))

private def outerGuards (bound : Bound) (inner : Nat) : Nat → Nat → Expr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1)) (word ordinal))
          (.letE (innerBound bound inner ordinal) (innerGuards ordinal inner 0)) .unit)
        (outerGuards bound inner remaining (ordinal + 1))

private def nestedExpression (stepBody : Expr) (outer inner : Nat) (bound : Bound) : Expr :=
  .letE stepBody (.lambda .word .word
    (.letE (.binary .wordAnd (.var 0) (word outer))
      (.letE (.newCell .word (.var 1)) (outerGuards bound inner outer 0))))

def canonicalProgram (step : Aggregates.CheckedDAG) (outer inner : Nat) (bound : Bound) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := nestedExpression step.program.body outer inner bound
}

def appliedProgram (step : Aggregates.CheckedDAG) (outer inner : Nat) (bound : Bound)
    (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step outer inner bound).body (.word input)
}

/-- Measure the actual wrapper syntax with a one-node placeholder step. It is
only a size calculation; cases remeasure the complete program after generating
the step DAG. -/
def appliedOverhead (outer inner : Nat) (bound : Bound) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (nestedExpression (.word Word.zero) outer inner bound) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  outer : Nat
  inner : Nat
  bound : Bound
  outerAllowed : AllowedMask outer
  innerAllowed : AllowedMask inner
  checked : (canonicalProgram step outer inner bound).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.outer plan.inner plan.bound

def ofParts? (step : Aggregates.CheckedDAG) (outer inner : Nat) (bound : Bound) : Option CheckedPlan :=
  if outerAllowed : AllowedMask outer then
    if innerAllowed : AllowedMask inner then
      if checked : (canonicalProgram step outer inner bound).check = true then
        some ⟨step, outer, inner, bound, outerAllowed, innerAllowed, checked⟩
      else none
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.outer plan.inner plan.bound input

theorem instantiate_wellTyped (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).WellTyped := by
  refine ⟨plan.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, appliedProgram, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply plan.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  Program.check_complete (plan.instantiate_wellTyped input)

/-- The inner bound the source computes in outer iteration `ordinal`. -/
def innerTrips (plan : CheckedPlan) (input accumulator : Word) (ordinal : Nat) : Nat :=
  let mask := Word.ofNatModulo plan.inner
  match plan.bound with
  | .input => (input.bitAnd mask).val
  | .counter => ((Word.ofNatModulo (ordinal + 1)).bitAnd mask).val
  | .accumulator => (accumulator.bitAnd mask).val

/-- The outer iterations a call runs. -/
def outerTrips (plan : CheckedPlan) (input : Word) : Nat :=
  (input.bitAnd (Word.ofNatModulo plan.outer)).val

end CheckedPlan
end Solcore.Synthesis.Core.NestedLoop
end

section
-- leanmerge: from Solcore.Synthesis.Core.Recursion
/-! Bounded recursion has an independent, finite Core reference. The source
recurses to the depth `input & mask`, through one function or two that call
each other; this Core expression instead unrolls the frames into literal
ordinal guards over one accumulator cell, with no recursion and no counter.
The complete step DAG is evaluated once before the input is supplied. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Recursion

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-recursion-plan-v1"

/-- A call with mask `m` recurses at most `m` frames deep. -/
def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- How each frame with depth `d > 0` combines its single call at depth `d - 1`. -/
inductive Form where
  /-- `f(d, acc) = f(d - 1, step(acc))`. -/
  | tail
  /-- `f(d, acc) = step(f(d - 1, acc)) + d`. -/
  | nontail
  /-- `even(d, acc) = odd(d - 1, step(acc))` and `odd(d, acc) = even(d - 1, acc + d)`. -/
  | mutual
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Form

def all : List Form := [.tail, .nontail, .mutual]

def name : Form → String
  | .tail => "tail"
  | .nontail => "nontail"
  | .mutual => "mutual"

def ofString? : String → Option Form
  | "tail" => some .tail
  | "nontail" => some .nontail
  | "mutual" => some .mutual
  | _ => none

end Form

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- The work of ordinal `k`, after its `k` Unit binders, where the accumulator
cell, depth, input and step closure occupy indices `k` to `k + 3`. A `tail`
ordinal is the frame `k` levels from the top, a `nontail` ordinal the frame of
depth `k + 1` (innermost first), and a `mutual` ordinal alternates the two
functions from the top, the odd one adding its own depth `d - k`. -/
private def frame (form : Form) (ordinal : Nat) : Expr :=
  let accumulator : Expr := .var ordinal
  let stepped : Expr := .apply (.var (ordinal + 3)) (.loadCell accumulator)
  match form with
  | .tail => .storeCell accumulator stepped
  | .nontail => .storeCell accumulator (.binary .wordAdd stepped (word (ordinal + 1)))
  | .mutual =>
      if ordinal % 2 = 0 then .storeCell accumulator stepped
      else .storeCell accumulator
        (.binary .wordAdd (.loadCell accumulator) (.binary .wordSub (.var (ordinal + 1)) (word ordinal)))

private def guards (form : Form) : Nat → Nat → Expr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1)) (word ordinal)) (frame form ordinal) .unit)
        (guards form remaining (ordinal + 1))

private def recursionExpression (stepBody : Expr) (mask : Nat) (form : Form) : Expr :=
  .letE stepBody (.lambda .word .word
    (.letE (.binary .wordAnd (.var 0) (word mask))
      (.letE (.newCell .word (.var 1)) (guards form mask 0))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask : Nat) (form : Form) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := recursionExpression step.program.body mask form
}

def appliedProgram (step : Aggregates.CheckedDAG) (mask : Nat) (form : Form) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step mask form).body (.word input)
}

/-- Measure the actual wrapper syntax with a one-node placeholder step. It is
only a size calculation; cases remeasure the complete program after generating
the step DAG. -/
def appliedOverhead (mask : Nat) (form : Form) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (recursionExpression (.word Word.zero) mask form) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  form : Form
  allowed : AllowedMask mask
  checked : (canonicalProgram step mask form).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask plan.form

def ofParts? (step : Aggregates.CheckedDAG) (mask : Nat) (form : Form) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if checked : (canonicalProgram step mask form).check = true then
      some ⟨step, mask, form, allowed, checked⟩
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.mask plan.form input

theorem instantiate_wellTyped (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).WellTyped := by
  refine ⟨plan.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, appliedProgram, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply plan.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  Program.check_complete (plan.instantiate_wellTyped input)

/-- The recursion depth of a call, which is also its number of frames above the base. -/
def depth (plan : CheckedPlan) (input : Word) : Nat :=
  (input.bitAnd (Word.ofNatModulo plan.mask)).val

end CheckedPlan
end Solcore.Synthesis.Core.Recursion
end

section
-- leanmerge: from Solcore.Synthesis.Core.RecursiveLoop
/-! Bounded loops inside recursive frames have an independent, finite Core
reference. The source recurses to the depth `input & D` in one of the
`runtime-recursion` forms, and every frame of depth `e > 0` runs a while loop
of `e & I` iterations; this Core expression instead unrolls the frames into
literal ordinal guards over one accumulator cell, as for recursion, and every
run frame binds its trip count and unrolls inner ordinal guards, as for nested
loops. There is no recursion, loop or counter cell. The complete step DAG is
evaluated once before the input is supplied. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.RecursiveLoop

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.Synthesis.Core.Recursion (Form)

def version : String := "core-recursive-loop-plan-v1"

/-- A depth mask `D` gives at most `D` frames; an inner mask `I` at most `I`
iterations in a frame. -/
def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3))

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- The depth of the frame of ordinal `k`, where the depth is index `k + 1`. A
`tail` or `mutual` ordinal is the frame `k` levels from the top; a `nontail`
ordinal is the frame of depth `k + 1`, innermost first. -/
private def frameDepth (form : Form) (ordinal : Nat) : Expr :=
  match form with
  | .nontail => word (ordinal + 1)
  | .tail | .mutual => .binary .wordSub (.var (ordinal + 1)) (word ordinal)

/-- One loop iteration of frame `k`, at inner ordinal `j`: the accumulator is
index `k + 1 + j`, the depth one further out and the step closure three. A
`mutual` frame at an odd ordinal is `sc_odd`, which adds its own depth. -/
private def work (form : Form) (frame inner : Nat) : Expr :=
  let accumulator := frame + 1 + inner
  match form with
  | .mutual =>
      if frame % 2 = 0 then .storeCell (.var accumulator)
        (.apply (.var (accumulator + 3)) (.loadCell (.var accumulator)))
      else .storeCell (.var accumulator) (.binary .wordAdd (.loadCell (.var accumulator))
        (.binary .wordSub (.var (accumulator + 1)) (word frame)))
  | .tail | .nontail => .storeCell (.var accumulator)
      (.apply (.var (accumulator + 3)) (.loadCell (.var accumulator)))

/-- Inside frame `k`, after its trip count and `j` Unit binders, the trip count
is index `j`. A `nontail` frame adds its depth after its loop. -/
private def innerGuards (form : Form) (frame : Nat) : Nat → Nat → Expr
  | 0, inner =>
      match form with
      | .nontail =>
          let accumulator := frame + 1 + inner
          .storeCell (.var accumulator) (.binary .wordAdd (.loadCell (.var accumulator)) (word (frame + 1)))
      | .tail | .mutual => .unit
  | remaining + 1, inner =>
      .letE (.ifE (.binary .wordGt (.var inner) (word inner)) (work form frame inner) .unit)
        (innerGuards form frame remaining (inner + 1))

/-- After its `k` Unit binders, frame `k` sees the accumulator cell, depth,
input and step closure at indices `k` to `k + 3`. -/
private def frames (form : Form) (innerMask : Nat) : Nat → Nat → Expr
  | 0, ordinal => .loadCell (.var ordinal)
  | remaining + 1, ordinal =>
      .letE (.ifE (.binary .wordGt (.var (ordinal + 1)) (word ordinal))
          (.letE (.binary .wordAnd (frameDepth form ordinal) (word innerMask))
            (innerGuards form ordinal innerMask 0)) .unit)
        (frames form innerMask remaining (ordinal + 1))

private def recursiveLoopExpression (stepBody : Expr) (depthMask innerMask : Nat) (form : Form) : Expr :=
  .letE stepBody (.lambda .word .word
    (.letE (.binary .wordAnd (.var 0) (word depthMask))
      (.letE (.newCell .word (.var 1)) (frames form innerMask depthMask 0))))

def canonicalProgram (step : Aggregates.CheckedDAG) (depthMask innerMask : Nat) (form : Form) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := recursiveLoopExpression step.program.body depthMask innerMask form
}

def appliedProgram (step : Aggregates.CheckedDAG) (depthMask innerMask : Nat) (form : Form)
    (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step depthMask innerMask form).body (.word input)
}

/-- Measure the actual wrapper syntax with a one-node placeholder step. It is
only a size calculation; cases remeasure the complete program after generating
the step DAG. -/
def appliedOverhead (depthMask innerMask : Nat) (form : Form) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (recursiveLoopExpression (.word Word.zero) depthMask innerMask form) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  depthMask : Nat
  innerMask : Nat
  form : Form
  depthAllowed : AllowedMask depthMask
  innerAllowed : AllowedMask innerMask
  checked : (canonicalProgram step depthMask innerMask form).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program :=
  canonicalProgram plan.step plan.depthMask plan.innerMask plan.form

def ofParts? (step : Aggregates.CheckedDAG) (depthMask innerMask : Nat) (form : Form) :
    Option CheckedPlan :=
  if depthAllowed : AllowedMask depthMask then
    if innerAllowed : AllowedMask innerMask then
      if checked : (canonicalProgram step depthMask innerMask form).check = true then
        some ⟨step, depthMask, innerMask, form, depthAllowed, innerAllowed, checked⟩
      else none
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.depthMask plan.innerMask plan.form input

theorem instantiate_wellTyped (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).WellTyped := by
  refine ⟨plan.wellTyped.dataDefinitionsWellFormed, ?_, ?_⟩
  · exact .word
  · simp only [instantiate, appliedProgram, Program.toCore, Expr.toCore, Ty.toCore, List.map_nil]
    exact .apply plan.wellTyped.bodyHasType (.word (value := input))

theorem instantiate_checked (plan : CheckedPlan) (input : Word) :
    (plan.instantiate input).check = true :=
  Program.check_complete (plan.instantiate_wellTyped input)

/-- The recursion depth of a call, which is also its number of frames above the base. -/
def depth (plan : CheckedPlan) (input : Word) : Nat :=
  (input.bitAnd (Word.ofNatModulo plan.depthMask)).val

/-- The loop iterations of a call: `e & I` for every frame depth `e` from one to the call's depth. -/
def iterations (plan : CheckedPlan) (input : Word) : Nat :=
  ((List.range (plan.depth input)).map fun frame =>
    ((Word.ofNatModulo (frame + 1)).bitAnd (Word.ofNatModulo plan.innerMask)).val).sum

end CheckedPlan
end Solcore.Synthesis.Core.RecursiveLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallGraphLoopEmitter
/-! Emit a bounded source while loop around a scalar call-graph step. Helpers
and the arbitrary entry use the call-graph renderer and raw primitive aliases;
the entry is always `sc_step`. The older aggregate loop emitter is unchanged.
`ScalarMeaning.CallGraphLoop.emit_source_meaning` relates the emitted text to
the original Core result under an independent fuel-indexed loop semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphLoop

open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-call-graph-loops-v2"
def wrapperVersion : String := "solcore-word-call-graph-loops-contract-v1"
def contractName : String := "SynthesizedCallGraphLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedCallGraphLoopsDeploy"]
def runtimePath : List String := ["SynthesizedCallGraphLoopsDeploy", "SynthesizedCallGraphLoops"]

def helperName (index : Nat) : String := "sc_fn" ++ toString index

/-- The source counter is independent of the Core ordinal guards. Each helper
and the step have fresh local temporaries that cannot shadow wrapper names. -/
def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    Primitive.opcodeImport, ""]
  for (body, index) in plan.graph.helpers.zipIdx do
    let rendered ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 body
    let name := helperName index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ rendered.value ++ ";", "}", ""]
    names := name :: names
  let entry ← CallGraphRenderer.renderWithFunctions names .word ["sc_arg"] 4 0 plan.graph.entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ entry.value ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallGraphLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.LoopEmitter
/-! Emit an actual source while loop. Its counter implementation is separate
from the finite ordinal guards in the checked Core reference. Every arbitrary
aggregate-DAG entry is emitted as `sc_step`; the last helper is not assumed to
be the entry. `ScalarMeaning.Loop.emit_source_meaning` relates the emitted
text to the original Core result under an independent fuel-indexed loop
semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Loop

open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-loops-v3"
def wrapperVersion : String := "solcore-word-loops-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedLoopsDeploy"]
def runtimePath : List String := ["SynthesizedLoopsDeploy", "SynthesizedLoops"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_acc = sc_step(sc_acc);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Loop
end

section
-- leanmerge: from Solcore.Synthesis.Source.LoopCases
/-! A loop case retains its checked step DAG, mask and independently executable
canonical Core reference. Every origin reconstructs the full reference before
replay; source execution uses a real while loop instead of its ordinal guards. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Loop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-loop-case.v1"
def planSchema : String := "solcore-lean.loop-plan.v1"
def profileVersion : String := "runtime-loops-v2/bounded-while-seed-v1"
def templateVersion : String := "bounded-word-loops-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.ofNatModulo 7,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let some plan := CheckedPlan.ofParts? step mask |
    throw "loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do throw "saved loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied loop exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("loopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson BoundedLoop.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "loopPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical loop plan and runtime input"
  return ⟨plan, input⟩

def maskFor (seed : Seed) : Nat :=
  match seed.toNat / 3 % 3 with
  | 0 => 1
  | 1 => 3
  | _ => 7

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let mask := maskFor seed
  let overhead := BoundedLoop.appliedOverhead mask
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected loop mask or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step mask |
    throw "generated loop plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied loop exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("mask", toJson mask), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "loop boundary observation produced a Core fault"

/-- Zero-trip inputs always return their original input, so varying final values
alone would be vacuous. A generated loop must also change a positive-trip input. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless (boundaryInputs.zip results).any (fun (input, result) =>
      (input.bitAnd (Word.ofNatModulo plan.mask)).val > 0 && result != input) do
    throw "all positive-trip boundary inputs returned their original input"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", BoundedLoop.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "loop-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported loop case origin"
  if kind = "loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "mask", "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated loop provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (mask : Nat) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if bounded : candidate.plan.mask ≤ source.plan.mask then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, bounded, strict⟩
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Shrinking the mask
intentionally removes complete canonical guards, never arbitrary Core scopes. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × Nat × Word) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, source.plan.mask, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < source.plan.mask then raw := raw ++ [(source.plan.step, mask, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(source.plan.step, source.plan.mask, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, mask, input) in raw do
    if let some reduced := sealReduction source step mask input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Loop
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallGraphLoopCases
/-! Replayable bounded loops over directly generated scalar call graphs. Every
origin reconstructs the canonical finite Core reference from the saved scalar
graph and mask; source execution uses a real while loop. The older loop and
call-graph profiles and their replay rules remain unchanged. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallGraphLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-call-graph-loop-case.v1"
def planSchema : String := "solcore-lean.call-graph-loop-plan.v1"
def profileVersion : String := "runtime-call-graph-loops-v1/direct-grammar-bounded-while-v1"
def functionVersion : String := Solcore.Synthesis.Core.CallGraphLoop.version
def generatorVersion : String := Solcore.Synthesis.Core.CallGraphLoop.grammarVersion
def boundaryVersion : String := "word-loop-boundary-bank-v1"
def stepBoundaryVersion : String := CallGraph.boundaryVersion
def callShapeVersion : String := CallGraph.callShapeVersion

/-- Iteration counts 0, 1, 3 and 7 under mask seven, plus both Word extremes. -/
def boundaryInputs : List Word := Loop.boundaryInputs

def inputWord := CallGraph.inputWord

def callShapes (plan : CheckedPlan) : List String := CallGraph.callShapes plan.graph

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.graph.program),
  ("mask", toJson plan.mask)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported call-graph loop plan schema"
  let graph ← CallGraph.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let some plan := CheckedPlan.ofParts? graph mask |
    throw "call-graph loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved call-graph loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied call-graph loop exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("loopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson functionVersion), ("loopVersion", toJson BoundedLoop.version),
    ("stepFunctionVersion", toJson wordFunctionDAGVersion),
    ("aggregateVersion", toJson Aggregates.version),
    ("boundaryVersion", toJson boundaryVersion),
    ("stepBoundaryVersion", toJson stepBoundaryVersion),
    ("callShapeVersion", toJson callShapeVersion),
    ("generatorVersion", toJson generatorVersion),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.features),
    ("helperCount", toJson plan.graph.helpers.length), ("callShapes", toJson (callShapes plan))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied call-graph loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel

/-- Even imported and reduced cases retain the exact canonical reference; no
origin makes a saved arbitrary Core program trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic call-graph loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "loopPlan")
  let input ← inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical call-graph loop plan and runtime input"
  let admitted : CheckedInput := ⟨plan, input⟩
  unless Wire.encodeProgram admitted.program == (← json.getObjVal? "program") do
    throw "saved Core call-graph loop application is not canonical"
  return admitted

def generatedPlan (seed : Seed) (nodes : Nat) : Except String (CheckedPlan × Json) := do
  let generated ← (Solcore.Synthesis.Core.CallGraphLoop.generate
    {seed, maxProgramNodes := nodes}).mapError reprStr
  let step := generated.step
  let stepOrigin := Json.mkObj [
    ("kind", toJson "call-graph-generated"),
    ("seed", toJson (toString step.initialSeed.toNat)),
    ("finalSeed", toJson (toString step.finalSeed.toNat)),
    ("maxProgramNodes", toJson step.maxProgramNodes),
    ("helperCount", toJson step.function.helpers.length),
    ("bodyBudgets", toJson step.bodyBudgets)]
  let origin := Json.mkObj [
    ("kind", toJson "call-graph-loop-generated"),
    ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes),
    ("mask", toJson generated.plan.mask), ("stepBudget", toJson generated.stepBudget),
    ("stepOrigin", stepOrigin)]
  return (generated.plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "loop boundary observation produced a Core fault"

/-- The step must contain an entry call and vary across the primitive bank.
Zero-trip inputs return themselves, so a positive-trip input must also change.
These are original Core observations, not executed source or opcode coverage. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  CallGraph.inputSensitive plan.graph fuel
  let results ← boundaryResults plan fuel
  unless (boundaryInputs.zip results).any (fun (input, result) =>
      (input.bitAnd (Word.ofNatModulo plan.mask)).val > 0 && result != input) do
    throw "all positive-trip boundary inputs returned their original input"

/-- Attempts count complete plan candidates. Accepted plans yield up to six
cases in fixed input order. Fuel exhaustion is an inconclusive exclusion. -/
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
        unless fuel ≤ 10000000 do throw "validation fuel exceeds profile limit"
        let (plan, origin) ← generatedPlan seed nodes
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-graph-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel)
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds profile limit"
  let admitted ← caseProgram json
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds profile limit"
  let provenance ← json.getObjVal? "provenance"
  for (name, expected) in [
      ("generatorVersion", generatorVersion), ("profileVersion", profileVersion),
      ("functionVersion", functionVersion), ("loopVersion", BoundedLoop.version),
      ("stepFunctionVersion", wordFunctionDAGVersion), ("aggregateVersion", Aggregates.version),
      ("boundaryVersion", boundaryVersion), ("stepBoundaryVersion", stepBoundaryVersion),
      ("callShapeVersion", callShapeVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical call-graph loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the call-graph loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.features do
    throw "saved features differ from the original Core call graph"
  unless (← provenance.getObjValAs? Nat "helperCount") = admitted.plan.graph.helpers.length do
    throw "saved helper count differs from the original Core call graph"
  unless (← provenance.getObjVal? "callShapes") == toJson (callShapes admitted.plan) do
    throw "saved call shapes differ from the original Core call graph"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-graph-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes
    unless planJson plan == planJson admitted.plan do
      throw "saved call-graph loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == inputSelection.record canonicalOrigin do throw "generated call-graph loop provenance is not canonical"
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do
      throw "imported call-graph loop provenance is not canonical"
  else if kind = "reduced" then
    let parentPlan ← origin.getObjVal? "parentPlan"
    let parentText ← origin.getObjValAs? String "parentInput"
    let parent : CheckedInput := ⟨← checkedPlan parentPlan, ← inputWord parentText⟩
    unless admitted.plan.graph.helpers.length = parent.plan.graph.helpers.length do
      throw "saved loop reduction changes helper count"
    unless admitted.plan.mask ≤ parent.plan.mask do
      throw "saved loop reduction increases its mask"
    unless (complexity admitted.program.body).isStrictlySmaller (complexity parent.program.body) do
      throw "saved loop reduction is not strictly smaller than its checked parent"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", parentPlan),
        ("parentInput", toJson parentText)] do
      throw "reduced call-graph loop provenance is not canonical"
  else throw "unsupported call-graph loop case origin"
  let fresh := makeCase admitted.plan admitted.input emitted origin fuel
  unless (← fresh.getObjVal? "provenance") == provenance do
    throw "call-graph loop provenance contains unexpected fields"
  -- Ignore the saved observation, but require the complete canonical envelope.
  let _ ← json.getObjVal? "directCore"
  let savedEnvelope := json.setObjVal! "directCore" .null
  let freshEnvelope := (fresh.setObjVal! "directCore" .null).setObjVal!
    "executionFuel" (toJson savedFuel)
  unless savedEnvelope == freshEnvelope do throw "saved call-graph loop case envelope is not canonical"
  return fresh

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.graph.helpers.length = source.plan.graph.helpers.length
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (graph : CheckedWordFunctionDAG)
    (mask : Nat) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? graph mask
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.graph.helpers.length = source.plan.graph.helpers.length then
    if bounded : candidate.plan.mask ≤ source.plan.mask then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
        some ⟨candidate, count, bounded, strict⟩
      else none
    else none
  else none

/-- Typed scalar graph reductions keep every helper binding. Smaller masks
remove complete canonical guards; every candidate is resealed as a plan. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (CheckedWordFunctionDAG × Nat × Word) := []
  for reduced in CallGraph.reductions ⟨source.plan.graph, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, source.plan.mask, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < source.plan.mask then raw := raw ++ [(source.plan.graph, mask, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(source.plan.graph, source.plan.mask, input)]
  let mut seen : List String := []
  let mut result := []
  for (graph, mask, input) in raw do
    if let some reduced := sealReduction source graph mask input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
      ("parentInput", toJson (toString source.input.val))]
    cases := cases.push (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.CallGraphLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.LoopClosureEmitter
/-! Emit an actual source while loop whose body creates a fresh closure with
`let`, capturing a loop-carried Word local, and applies it in the same
iteration after that local changes. This implementation is separate from the
finite ordinal guards and snapshot lambdas of the checked Core reference. The
aggregate step DAG is emitted as `sc_step`, as for loops. No emitter proof
covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.LoopClosure

open Solcore.Synthesis.Core.LoopClosure (CheckedPlan Capture)

def emitterVersion : String := "solcore-source-loop-closures-v2"
def wrapperVersion : String := "solcore-word-loop-closures-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedLoopClosures"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedLoopClosuresDeploy"]
def runtimePath : List String := ["SynthesizedLoopClosuresDeploy", "SynthesizedLoopClosures"]

/-- The loop body of a capture. -/
def body : Capture → List String
  | .accumulator => [
      "            let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "                return sc_step(sc_acc + sc_arg);", "            };",
      "            sc_acc = (sc_acc + 1);",
      "            sc_acc = (sc_f(sc_counter) + sc_acc);",
      "            sc_counter = (sc_counter + 1);"]
  | .counter => [
      "            let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "                return (sc_step(sc_arg) + sc_counter);", "            };",
      "            sc_counter = (sc_counter + 1);",
      "            sc_acc = sc_apply(sc_f, sc_acc);"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", ""]
  for (helper, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 helper
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_counter: word = 0;",
    "        while (sc_limit > sc_counter) {"] ++ body plan.capture ++ [
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.LoopClosure
end

section
-- leanmerge: from Solcore.Synthesis.Source.LoopClosureCases
/-! A loop-closure case retains its checked step DAG, mask, capture and the
independently executable canonical Core reference. Every origin reconstructs
the full reference before replay; source execution creates a real closure in
every iteration of a real while loop instead of running the ordinal guards. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.LoopClosure
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.LoopClosure (CheckedPlan Capture)

def caseSchema : String := "solcore-lean.semantic-loop-closure-case.v1"
def planSchema : String := "solcore-lean.loop-closure-plan.v1"
def profileVersion : String := "runtime-loop-closures-v1/capture-mask-seed-v1"
def templateVersion : String := "bounded-word-loop-closures-v1"

/-- Zero, one, three and seven iterations under mask seven, as for loops. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.ofNatModulo 7,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask), ("capture", toJson plan.capture.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported loop-closure plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let some capture := Capture.ofString? (← json.getObjValAs? String "capture") |
    throw "loop-closure capture must be accumulator or counter"
  let some plan := CheckedPlan.ofParts? step mask capture |
    throw "loop-closure plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved loop-closure plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied loop closure exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("loopClosurePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson LoopClosure.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied loop closure exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic loop-closure case schema"
  let plan ← checkedPlan (← json.getObjVal? "loopClosurePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical loop-closure plan and runtime input"
  return ⟨plan, input⟩

/-- The six generation shapes: each capture at masks one, three and seven. -/
def shapes : List (Nat × Capture) :=
  Capture.all.flatMap fun capture => [(1, capture), (3, capture), (7, capture)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x6c6f6f70636c6f01

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Capture :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (7, .accumulator)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (mask, capture) := shapeFor seed
  let overhead := LoopClosure.appliedOverhead mask capture
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected loop-closure shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step mask capture |
    throw "generated loop-closure plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied loop closure exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "loop-closure-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("mask", toJson mask), ("capture", toJson capture.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "loop-closure boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "loop-closure boundary observation produced a Core fault"

/-- Zero-trip inputs always return their original input, so a generated loop
closure must change a positive-trip input, as a generated loop must. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless (boundaryInputs.zip results).any (fun (input, result) => plan.iterations input > 0 && result != input) do
    throw "all positive-trip boundary inputs returned their original input"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "loop-closure-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", LoopClosure.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical loop-closure plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the loop-closure wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "loop-closure-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported loop-closure case origin"
  if kind = "loop-closure-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "mask", "capture", "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated loop-closure provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved loop-closure plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its loop-closure boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameCapture : candidate.plan.capture = source.plan.capture
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (mask : Nat) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask source.plan.capture
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if capture : candidate.plan.capture = source.plan.capture then
        if bounded : candidate.plan.mask ≤ source.plan.mask then
          if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
            some ⟨candidate, count, bindings, capture, bounded, strict⟩
          else none
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Shrinking the mask
removes complete canonical guards, never arbitrary Core scopes; the capture is
kept. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × Nat × Word) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, source.plan.mask, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < source.plan.mask then raw := raw ++ [(source.plan.step, mask, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(source.plan.step, source.plan.mask, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, mask, input) in raw do
    if let some reduced := sealReduction source step mask input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.LoopClosure
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedLoopEmitter
/-! Emit an actual source while loop whose body runs a second while loop. Both
counters, the inner bound and the accumulator are declared before the outer
loop and assigned inside it; this implementation is separate from the finite
ordinal guards of the checked Core reference. The aggregate step DAG is
emitted as `sc_step`, as for single loops. No emitter proof covers this
wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedLoop

open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)

def emitterVersion : String := "solcore-source-nested-loops-v2"
def wrapperVersion : String := "solcore-word-nested-loops-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedNestedLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedNestedLoopsDeploy"]
def runtimePath : List String := ["SynthesizedNestedLoopsDeploy", "SynthesizedNestedLoops"]

/-- The inner bound the wrapper assigns at the start of each outer iteration. -/
def innerBoundSource (plan : CheckedPlan) : String :=
  match plan.bound with
  | .input => "(sc_input & " ++ toString plan.inner ++ ")"
  | .counter => "((sc_i + 1) & " ++ toString plan.inner ++ ")"
  | .accumulator => "(sc_acc & " ++ toString plan.inner ++ ")"

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_outer: word = (sc_input & " ++ toString plan.outer ++ ");",
    "        let sc_acc: word = sc_input;",
    "        let sc_i: word = 0;",
    "        let sc_inner: word = 0;",
    "        let sc_j: word = 0;",
    "        while (sc_outer > sc_i) {",
    "            sc_inner = " ++ innerBoundSource plan ++ ";",
    "            sc_j = 0;",
    "            while (sc_inner > sc_j) {",
    "                sc_acc = sc_step(sc_acc);",
    "                sc_j = (sc_j + 1);",
    "            }",
    "            sc_i = (sc_i + 1);",
    "        }",
    "        return uint256(sc_acc);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.NestedLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedLoopCases
/-! A nested-loop case retains its checked step DAG, both masks, the inner
bound form and the independently executable canonical Core reference. Every
origin reconstructs the full reference before replay; source execution runs
two real while loops instead of the ordinal guards. A case also records the
inner trip count of every outer iteration it runs, specified by the plan, the
input and the step's original Core results, not measured. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedLoop (CheckedPlan Bound)

def caseSchema : String := "solcore-lean.semantic-nested-loop-case.v1"
def planSchema : String := "solcore-lean.nested-loop-plan.v1"
def profileVersion : String := "runtime-nested-loops-v1/bounded-while-seed-v1"
def templateVersion : String := "bounded-nested-word-loops-v1"

/-- Zero to three outer iterations under the outer mask three. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 3,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("outerMask", toJson plan.outer), ("innerMask", toJson plan.inner),
  ("innerBound", toJson plan.bound.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported nested loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let outer ← json.getObjValAs? Nat "outerMask"
  let inner ← json.getObjValAs? Nat "innerMask"
  let some bound := Bound.ofString? (← json.getObjValAs? String "innerBound") |
    throw "unsupported nested loop inner bound"
  let some plan := CheckedPlan.ofParts? step outer inner bound |
    throw "nested loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved nested loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied nested loop exceeds the 512-node case limit"
  return plan

/-- The step's original Core result for one call. -/
def stepResult (plan : CheckedPlan) (value : Word) (fuel : Nat) : Option Word :=
  match (plan.step.instantiate value).toCore.runStateful fuel with
  | .done (.word result) _ => some result
  | _ => none

/-- The inner trip count of each outer iteration a call runs and the final
accumulator, evaluating the step's original Core call by call. `none` when a
step call does not return a Word within the fuel. -/
def simulate (plan : CheckedPlan) (input : Word) (fuel : Nat) : Option (List Nat × Word) := Id.run do
  let mut accumulator := input
  let mut trips : List Nat := []
  for ordinal in List.range (plan.outerTrips input) do
    let count := plan.innerTrips input accumulator ordinal
    for _ in List.range count do
      match stepResult plan accumulator fuel with
      | some value => accumulator := value
      | none => return none
    trips := trips ++ [count]
  return some (trips, accumulator)

def iterationsJson (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  match simulate plan input fuel with
  | some (trips, _) => toJson trips
  | none => .null

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("nestedLoopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson NestedLoop.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features), ("iterations", iterationsJson plan input fuel)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied nested loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic nested loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "nestedLoopPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical nested loop plan and runtime input"
  return ⟨plan, input⟩

/-- The twelve generation shapes: both masks from one and three, then the bound. -/
def shapes : List (Nat × Nat × Bound) :=
  Bound.all.flatMap fun bound => [(1, 1, bound), (1, 3, bound), (3, 1, bound), (3, 3, bound)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x6e65737465643031

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Nat × Bound :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (3, 3, .input)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (outer, inner, bound) := shapeFor seed
  let overhead := NestedLoop.appliedOverhead outer inner bound
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected nested loop shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step outer inner bound |
    throw "generated nested loop plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied nested loop exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "nested-loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("outerMask", toJson outer), ("innerMask", toJson inner), ("innerBound", toJson bound.name),
    ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "nested loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "nested loop boundary observation produced a Core fault"

/-- A boundary input without a step call returns itself, so a generated nested
loop must change some boundary input. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  if results == boundaryInputs then throw Acceptance.identityReason

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "nested-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", NestedLoop.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical nested loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the nested loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let savedFuel ← json.getObjValAs? Nat "executionFuel"
  unless savedFuel ≤ 10000000 do throw "saved execution fuel exceeds limit"
  unless (← provenance.getObjVal? "iterations") == iterationsJson admitted.plan admitted.input savedFuel do
    throw "saved iterations differ from the plan, input and step"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "nested-loop-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported nested loop case origin"
  if kind = "nested-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "outerMask", "innerMask", "innerBound",
        "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated nested loop provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved nested loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its nested loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedOuter : candidate.plan.outer ≤ source.plan.outer
  boundedInner : candidate.plan.inner ≤ source.plan.inner
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (outer inner : Nat) (bound : Bound) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step outer inner bound
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if boundedOuter : candidate.plan.outer ≤ source.plan.outer then
        if boundedInner : candidate.plan.inner ≤ source.plan.inner then
          if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
            some ⟨candidate, count, bindings, boundedOuter, boundedInner, strict⟩
          else none
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Lowering a mask
removes complete canonical guards and the input bound replaces a larger inner
bound expression; neither removes an arbitrary Core scope. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let plan := source.plan
  let mut raw : List (Aggregates.CheckedDAG × Nat × Nat × Bound × Word) := []
  for reduced in Aggregate.reductions ⟨plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, plan.outer, plan.inner, plan.bound, reduced.candidate.input)]
  for outer in [0, 1] do
    if outer < plan.outer then raw := raw ++ [(plan.step, outer, plan.inner, plan.bound, source.input)]
  for inner in [0, 1] do
    if inner < plan.inner then raw := raw ++ [(plan.step, plan.outer, inner, plan.bound, source.input)]
  if plan.bound != .input then raw := raw ++ [(plan.step, plan.outer, plan.inner, .input, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(plan.step, plan.outer, plan.inner, plan.bound, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, outer, inner, bound, input) in raw do
    if let some reduced := sealReduction source step outer inner bound input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.NestedLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.RecursionEmitter
/-! Emit an actual recursive source function, or two functions that call each
other, to the depth `input & mask`. Each function makes one call at depth
`d - 1` when `d > 0`, assigning its single result local in both branches of
one `if`; this implementation is separate from the finite ordinal guards of
the checked Core reference. The aggregate step DAG is emitted as `sc_step`, as
for loops. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Recursion

open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)

def emitterVersion : String := "solcore-source-recursion-v2"
def wrapperVersion : String := "solcore-word-recursion-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedRecursion"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRecursionDeploy"]
def runtimePath : List String := ["SynthesizedRecursionDeploy", "SynthesizedRecursion"]

/-- One recursive function: `recurse` is its body when `sc_depth > 0`. -/
private def recursive (name : String) (recurse : List String) : List String :=
  ["function " ++ name ++ "(sc_depth: word, sc_acc: word) returns (word) {",
    "    let sc_result: word = sc_acc;",
    "    if (sc_depth > 0) {"] ++ recurse.map ("        " ++ ·) ++
  ["    } else {", "        sc_result = sc_acc;", "    }", "    return sc_result;", "}", ""]

/-- The recursive functions of a form, and the one the contract calls. -/
def recursion (form : Form) : List String × String :=
  match form with
  | .tail =>
      (recursive "sc_rec" ["let sc_next: word = sc_step(sc_acc);", "sc_result = sc_rec((sc_depth - 1), sc_next);"],
        "sc_rec")
  | .nontail =>
      (recursive "sc_rec" ["let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);",
        "let sc_stepped: word = sc_step(sc_inner);", "sc_result = (sc_stepped + sc_depth);"], "sc_rec")
  | .mutual =>
      (recursive "sc_even" ["let sc_next: word = sc_step(sc_acc);", "sc_result = sc_odd((sc_depth - 1), sc_next);"] ++
        recursive "sc_odd" ["let sc_next: word = (sc_acc + sc_depth);",
          "sc_result = sc_even((sc_depth - 1), sc_next);"], "sc_even")

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  let (functions, entryName) := recursion plan.form
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""] ++ functions ++
    ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_depth: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_out: word = " ++ entryName ++ "(sc_depth, sc_input);",
    "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Recursion
end

section
-- leanmerge: from Solcore.Synthesis.Source.RecursionCases
/-! A recursion case retains its checked step DAG, depth mask, recursion form
and the independently executable canonical Core reference. Every origin
reconstructs the full reference before replay; source execution makes real
recursive calls instead of running the ordinal guards. A case's depth is
`input & mask`, prescribed by the plan and the input. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Recursion
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Recursion (CheckedPlan Form)

def caseSchema : String := "solcore-lean.semantic-recursion-case.v1"
def planSchema : String := "solcore-lean.recursion-plan.v1"
def profileVersion : String := "runtime-recursion-v1/bounded-depth-seed-v1"
def templateVersion : String := "bounded-word-recursion-v1"

/-- Depths zero to three and seven under mask seven, and an even positive depth. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 3, Word.ofNatModulo 7,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("depthMask", toJson plan.mask), ("form", toJson plan.form.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported recursion plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "depthMask"
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "unsupported recursion form"
  let some plan := CheckedPlan.ofParts? step mask form |
    throw "recursion plan has an invalid depth mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved recursion plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied recursion exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("recursionPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Recursion.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied recursion exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic recursion case schema"
  let plan ← checkedPlan (← json.getObjVal? "recursionPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical recursion plan and runtime input"
  return ⟨plan, input⟩

/-- The nine generation shapes: each form at depth masks one, three and seven. -/
def shapes : List (Nat × Form) :=
  Form.all.flatMap fun form => [(1, form), (3, form), (7, form)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x7265637572736501

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Form :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (7, .tail)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (mask, form) := shapeFor seed
  let overhead := Recursion.appliedOverhead mask form
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected recursion shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step mask form |
    throw "generated recursion plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied recursion exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "recursion-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("depthMask", toJson mask), ("form", toJson form.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "recursion boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "recursion boundary observation produced a Core fault"

/-- A depth-zero input returns itself, so a generated recursion must change
some boundary input. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  if results == boundaryInputs then throw Acceptance.identityReason

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "recursion-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Recursion.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical recursion plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the recursion wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "recursion-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported recursion case origin"
  if kind = "recursion-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "depthMask", "form", "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated recursion provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved recursion plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its recursion boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedMask : candidate.plan.mask ≤ source.plan.mask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (mask : Nat) (form : Form) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask form
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if bounded : candidate.plan.mask ≤ source.plan.mask then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, bounded, strict⟩
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Lowering the depth
mask removes complete canonical guards and the tail form replaces larger
frames; neither removes an arbitrary Core scope. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let plan := source.plan
  let mut raw : List (Aggregates.CheckedDAG × Nat × Form × Word) := []
  for reduced in Aggregate.reductions ⟨plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, plan.mask, plan.form, reduced.candidate.input)]
  for mask in [0, 1, 3] do
    if mask < plan.mask then raw := raw ++ [(plan.step, mask, plan.form, source.input)]
  if plan.form != .tail then raw := raw ++ [(plan.step, plan.mask, .tail, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(plan.step, plan.mask, plan.form, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, mask, form, input) in raw do
    if let some reduced := sealReduction source step mask form input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Recursion
end

section
-- leanmerge: from Solcore.Synthesis.Source.RecursiveLoopEmitter
/-! Emit actual recursive source functions, as for `runtime-recursion`, in
which every frame with depth `e > 0` runs a while loop of `e & I` iterations,
with its trip count, counter and value declared in the frame. This
implementation is separate from the unrolled frame and inner ordinal guards of
the checked Core reference. The aggregate step DAG is emitted as `sc_step`, as
for loops. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RecursiveLoop

open Solcore.Synthesis.Core.RecursiveLoop (CheckedPlan)
open Solcore.Synthesis.Core.Recursion (Form)

def emitterVersion : String := "solcore-source-recursive-loops-v2"
def wrapperVersion : String := "solcore-word-recursive-loops-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedRecursiveLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRecursiveLoopsDeploy"]
def runtimePath : List String := ["SynthesizedRecursiveLoopsDeploy", "SynthesizedRecursiveLoops"]

/-- One recursive function: `recurse` is its body when `sc_depth > 0`. -/
private def recursive (name : String) (recurse : List String) : List String :=
  ["function " ++ name ++ "(sc_depth: word, sc_acc: word) returns (word) {",
    "    let sc_result: word = sc_acc;",
    "    if (sc_depth > 0) {"] ++ recurse.map ("        " ++ ·) ++
  ["    } else {", "        sc_result = sc_acc;", "    }", "    return sc_result;", "}", ""]

/-- The frame's while loop of `sc_depth & I` iterations over `value`. -/
private def loop (innerMask : Nat) (value update : String) : List String :=
  ["let sc_trips: word = (sc_depth & " ++ toString innerMask ++ ");", "let sc_j: word = 0;",
    "while (sc_trips > sc_j) {", "    " ++ value ++ " = " ++ update ++ ";", "    sc_j = (sc_j + 1);", "}"]

/-- The recursive functions of a form, and the one the contract calls. -/
def recursion (form : Form) (innerMask : Nat) : List String × String :=
  match form with
  | .tail =>
      (recursive "sc_rec" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "sc_step(sc_value)" ++
        ["sc_result = sc_rec((sc_depth - 1), sc_value);"]), "sc_rec")
  | .nontail =>
      (recursive "sc_rec" (["let sc_inner: word = sc_rec((sc_depth - 1), sc_acc);"] ++
        loop innerMask "sc_inner" "sc_step(sc_inner)" ++ ["sc_result = (sc_inner + sc_depth);"]), "sc_rec")
  | .mutual =>
      (recursive "sc_even" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "sc_step(sc_value)" ++
        ["sc_result = sc_odd((sc_depth - 1), sc_value);"]) ++
        recursive "sc_odd" (["let sc_value: word = sc_acc;"] ++ loop innerMask "sc_value" "(sc_value + sc_depth)" ++
          ["sc_result = sc_even((sc_depth - 1), sc_value);"]), "sc_even")

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ [""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  let (functions, entryName) := recursion plan.form plan.innerMask
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""] ++ functions ++
    ["contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_depth: word = (sc_input & " ++ toString plan.depthMask ++ ");",
    "        let sc_out: word = " ++ entryName ++ "(sc_depth, sc_input);",
    "        return uint256(sc_out);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.RecursiveLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.RecursiveLoopCases
/-! A recursive-loop case retains its checked step DAG, depth and inner masks,
recursion form and the independently executable canonical Core reference.
Every origin reconstructs the full reference before replay; source execution
makes real recursive calls and runs a real while loop in every frame instead of
running the ordinal guards. A case's depth is `input & D`, and a frame of depth
`e` runs `e & I` iterations, prescribed by the plan and the input. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.RecursiveLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.RecursiveLoop (CheckedPlan)
open Solcore.Synthesis.Core.Recursion (Form)

def caseSchema : String := "solcore-lean.semantic-recursive-loop-case.v1"
def planSchema : String := "solcore-lean.recursive-loop-plan.v1"
def profileVersion : String := "runtime-recursive-loops-v1/bounded-depth-loop-seed-v1"
def templateVersion : String := "bounded-word-recursive-loops-v1"

/-- Depths zero to three under depth mask three, as for nested loops. -/
def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 2, Word.ofNatModulo 3,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("depthMask", toJson plan.depthMask), ("innerMask", toJson plan.innerMask),
  ("form", toJson plan.form.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported recursive-loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let depthMask ← json.getObjValAs? Nat "depthMask"
  let innerMask ← json.getObjValAs? Nat "innerMask"
  let some form := Form.ofString? (← json.getObjValAs? String "form") |
    throw "unsupported recursive-loop form"
  let some plan := CheckedPlan.ofParts? step depthMask innerMask form |
    throw "recursive-loop plan has an invalid mask or failed the full Core checker"
  unless json == planJson plan do
    throw "saved recursive-loop plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied recursive loop exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("recursiveLoopPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson RecursiveLoop.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied recursive loop exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic recursive-loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "recursiveLoopPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical recursive-loop plan and runtime input"
  return ⟨plan, input⟩

/-- The twelve generation shapes: each form at depth masks one and three and
inner masks one and three. -/
def shapes : List (Nat × Nat × Form) :=
  Form.all.flatMap fun form => [(1, 1, form), (1, 3, form), (3, 1, form), (3, 3, form)]

/-- Separates the shape stream from other uses of a case seed. -/
private def shapeDomain : UInt64 := 0x7265636c6f6f7001

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in shape
independently of the step's helper count and template. -/
def shapeFor (seed : Seed) : Nat × Nat × Form :=
  shapes[(GeneratorV2.mix (seed.toUInt64 ^^^ shapeDomain)).toNat % shapes.length]?.getD (3, 3, .tail)

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let (depthMask, innerMask, form) := shapeFor seed
  let overhead := RecursiveLoop.appliedOverhead depthMask innerMask form
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected recursive-loop shape or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step depthMask innerMask form |
    throw "generated recursive-loop plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied recursive loop exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "recursive-loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("depthMask", toJson depthMask), ("innerMask", toJson innerMask), ("form", toJson form.name),
    ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "recursive-loop boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "recursive-loop boundary observation produced a Core fault"

/-- A depth-zero input returns itself, so a generated recursive loop must
change some boundary input, as a generated recursion must. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  if results == boundaryInputs then throw Acceptance.identityReason

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "recursive-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", RecursiveLoop.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical recursive-loop plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the recursive-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "recursive-loop-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported recursive-loop case origin"
  if kind = "recursive-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    for name in ["kind", "seed", "finalSeed", "maxProgramNodes", "depthMask", "innerMask", "form", "stepOrigin"] do
      unless (← origin.getObjVal? name) == (← expectedOrigin.getObjVal? name) do
        throw ("saved " ++ name ++ " differs from generated recursive-loop provenance")
    unless planJson plan == planJson admitted.plan do
      throw "saved recursive-loop plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its recursive-loop boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    inputSensitive plan validationFuel
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  boundedDepth : candidate.plan.depthMask ≤ source.plan.depthMask
  boundedInner : candidate.plan.innerMask ≤ source.plan.innerMask
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (depthMask innerMask : Nat) (form : Form) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step depthMask innerMask form
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if depth : candidate.plan.depthMask ≤ source.plan.depthMask then
        if inner : candidate.plan.innerMask ≤ source.plan.innerMask then
          if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
            some ⟨candidate, count, bindings, depth, inner, strict⟩
          else none
        else none
      else none
    else none
  else none

/-- Only the checked step's binders must remain unchanged. Lowering a mask
removes complete canonical frame or inner guards, and the tail form replaces
larger frames; neither removes an arbitrary Core scope. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let plan := source.plan
  let mut raw : List (Aggregates.CheckedDAG × Nat × Nat × Form × Word) := []
  for reduced in Aggregate.reductions ⟨plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, plan.depthMask, plan.innerMask, plan.form, reduced.candidate.input)]
  for mask in [0, 1] do
    if mask < plan.depthMask then raw := raw ++ [(plan.step, mask, plan.innerMask, plan.form, source.input)]
    if mask < plan.innerMask then raw := raw ++ [(plan.step, plan.depthMask, mask, plan.form, source.input)]
  if plan.form != .tail then raw := raw ++ [(plan.step, plan.depthMask, plan.innerMask, .tail, source.input)]
  for input in boundaryInputs do
    raw := raw ++ [(plan.step, plan.depthMask, plan.innerMask, plan.form, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, depthMask, innerMask, form, input) in raw do
    if let some reduced := sealReduction source step depthMask innerMask form input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.RecursiveLoop
end
