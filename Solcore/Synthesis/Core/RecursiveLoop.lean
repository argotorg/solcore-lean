import Solcore.Synthesis.Core.Recursion

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
