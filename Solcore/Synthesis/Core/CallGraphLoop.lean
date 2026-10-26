import Solcore.Synthesis.Core.BoundedLoop
import Solcore.Synthesis.Core.CallGraphGenerator

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
