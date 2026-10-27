import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

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
