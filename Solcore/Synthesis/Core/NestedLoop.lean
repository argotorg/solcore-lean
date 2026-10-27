import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

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
