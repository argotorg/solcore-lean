import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

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
