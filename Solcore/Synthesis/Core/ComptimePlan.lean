import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

/-! An independent reference for a source computation staged at compile time.
The complete original closed expression remains in Core and is evaluated once;
no constant obtained from Rust specialization or saved observations is trusted.
Its value feeds a checked runtime step through a fixed offset or scale wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Comptime

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-comptime-word-plan-v1"

inductive Variant where
  | offset
  | scale
  deriving Repr, BEq, DecidableEq

namespace Variant

def all : List Variant := [.offset, .scale]

def name : Variant → String
  | .offset => "offset"
  | .scale => "scale"

def ofString? : String → Option Variant
  | "offset" => some .offset
  | "scale" => some .scale
  | _ => none

end Variant

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- At the input lambda, input/step/constant occupy indices 0/1/2. Both
wrappers call the step exactly once and retain the complete closed expression. -/
private def runtimeBody : Variant → Expr
  | .offset =>
      .binary .wordAdd
        (.apply (.var 1) (.binary .wordAdd (.var 0) (.var 2))) (.var 2)
  | .scale =>
      .binary .wordAdd
        (.binary .wordMul (.apply (.var 1) (.var 0)) (.binary .wordOr (.var 2) (word 1)))
        (.var 2)

private def stagedExpression (constantBody stepBody : Expr) (variant : Variant) : Expr :=
  .letE constantBody (.letE stepBody (.lambda .word .word (runtimeBody variant)))

def canonicalProgram (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG)
    (variant : Variant) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := stagedExpression constant.program.body step.program.body variant
}

def appliedProgram (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG)
    (variant : Variant) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram constant step variant).body (.word input)
}

def canonicalNodes (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) (variant : Variant) : Nat :=
  programNodes (canonicalProgram constant step variant)

def appliedNodes (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) (variant : Variant) : Nat :=
  programNodes (appliedProgram constant step variant Word.zero)

/-- The fixed wrapper cost excludes both retained programs. Placeholders are
only syntax measurements; admission checks both full original expressions. -/
def appliedOverhead (variant : Variant) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (stagedExpression (.word Word.zero) (.word Word.zero) variant) (.word Word.zero)
  } - programNodes {
    resultType := .word, dataDefinitions := [], body := .word Word.zero
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  constant : CheckedWordProgram
  step : Aggregates.CheckedDAG
  variant : Variant
  checked : (canonicalProgram constant step variant).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.constant plan.step plan.variant

def ofParts? (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG)
    (variant : Variant) : Option CheckedPlan :=
  if checked : (canonicalProgram constant step variant).check = true then
    some ⟨constant, step, variant, checked⟩
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.constant plan.step plan.variant input

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
end Solcore.Synthesis.Core.Comptime
