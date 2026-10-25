import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

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
