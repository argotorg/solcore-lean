import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

/-! An independent Core reference for a fixed four-module source composition.
The original closed constant and aggregate step remain intact. Ordinary typed
closures model the imported apply and selector functions; explicit Word loads
preserve capture snapshots across assignments. Core needs no module primitive.
The checked plan certifies Core typing, not source-emitter preservation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Modules

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-module-composition-plan-v1"

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def wordFunction : Ty := .function .word .word

private def applyFunction : Expr :=
  .lambda wordFunction wordFunction (.lambda .word .word (.apply (.var 1) (.var 0)))

private def selectFunction : Expr :=
  .lambda .bool (.function .word wordFunction)
    (.lambda .word wordFunction
      (.lambda .word .word (.ifE (.var 2) (.var 1) (.var 0))))

/-- Load the captured local before constructing the closure. Its body reads
the immutable Word at index one, never the mutable cell reference. -/
private def capture : Expr :=
  .letE (.loadCell (.var 0))
    (.lambda .word .word (.binary .wordAdd (.var 1) (.var 0)))

/-- The outer context is select/apply/step/constant. After both parameters,
it is k/input/select/apply/step/constant. Local binders are cap, f, Unit, a. -/
private def leftFunction : Expr :=
  .lambda .word wordFunction
    (.lambda .word .word
      (.letE (.newCell .word (.apply (.var 4) (.binary .wordAdd (.var 1) (.var 0))))
        (.letE capture
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 1)))
            (.letE (.apply (.apply (.var 6) (.var 1)) (.var 4))
              (.binary .wordAdd (.var 0) (.loadCell (.var 3))))))))

/-- The outer context adds left before select/apply/step/constant. This second
closure captures its own local; applying it cannot observe the left cell. -/
private def rightFunction : Expr :=
  .lambda .word wordFunction
    (.lambda .word .word
      (.letE (.newCell .word (.binary .wordXor (.var 1) (.var 0)))
        (.letE capture
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 2)))
            (.letE (.apply (.apply (.var 7) (.var 1)) (.binary .wordAdd (.var 4) (word 1)))
              (.binary .wordAdd (.var 0) (.loadCell (.var 3))))))))

/-- At the public lambda: input/right/left/select/apply/step/constant.
Evaluate both providers left-to-right, then invoke the selector and combine all
three results with the original constant. No provider's result is inert. -/
private def entryFunction : Expr :=
  .lambda .word .word
    (.letE (.apply (.apply (.var 2) (.var 0)) (.var 6))
      (.letE (.apply (.apply (.var 2) (.var 1)) (.var 7))
        (.letE (.binary .wordEq (.binary .wordAnd (.var 2) (word 1)) (word 1))
          (.letE (.apply (.apply (.apply (.var 6) (.var 0)) (.var 2)) (.var 1))
            (.binary .wordAdd
              (.binary .wordAdd (.binary .wordAdd (.var 0) (.var 3))
                (.binary .wordMul (word 3) (.var 2)))
              (.var 10))))))

private def composedExpression (constantBody stepBody : Expr) : Expr :=
  .letE constantBody
    (.letE stepBody
      (.letE applyFunction
        (.letE selectFunction
          (.letE leftFunction (.letE rightFunction entryFunction)))))

def canonicalProgram (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := composedExpression constant.program.body step.program.body
}

def appliedProgram (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG)
    (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram constant step).body (.word input)
}

def canonicalNodes (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) : Nat :=
  programNodes (canonicalProgram constant step)

def appliedNodes (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) : Nat :=
  programNodes (appliedProgram constant step Word.zero)

/-- Measure the fixed composition, excluding both retained programs. These
one-node placeholders are measurements only; admission checks the full AST. -/
def appliedOverhead : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (composedExpression (.word Word.zero) (.word Word.zero)) (.word Word.zero)
  } - programNodes {
    resultType := .word, dataDefinitions := [], body := .word Word.zero
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  constant : CheckedWordProgram
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram constant step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.constant plan.step

def ofParts? (constant : CheckedWordProgram) (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram constant step).check = true then
    some ⟨constant, step, checked⟩
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.constant plan.step input

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
end Solcore.Synthesis.Core.Modules
