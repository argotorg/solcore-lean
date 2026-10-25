import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

/-! Checked local closures with Word snapshot captures. Source locals may be
assigned after closure creation; the Core closure therefore captures an explicit
loaded Word, not the reference of the mutable outer cell. No evaluator changes
or source-emitter correspondence assumptions are needed for this reference. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Closure

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-closure-capture-plan-v1"

inductive Variant where
  | snapshot
  | independent
  deriving Repr, BEq, DecidableEq

namespace Variant

def all : List Variant := [.snapshot, .independent]

def name : Variant → String
  | .snapshot => "snapshot"
  | .independent => "independent"

def ofString? : String → Option Variant
  | "snapshot" => some .snapshot
  | "independent" => some .independent
  | _ => none

end Variant

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def wordFunction : Ty := .function .word .word

/-- The source's generic higher-order apply function, instantiated at Word. -/
private def applyFunction : Expr :=
  .lambda wordFunction wordFunction (.lambda .word .word (.apply (.var 1) (.var 0)))

/-- Read the mutable outer local now. Inside the resulting lambda, index one
is that immutable Word snapshot; index zero is the call's argument. -/
private def capture (reference : Nat) : Expr :=
  .letE (.loadCell (.var reference))
    (.lambda .word .word (.binary .wordAdd (.var 1) (.var 0)))

private def secondClosure : Variant → Expr
  | .snapshot => .var 1
  | .independent => capture 2

/-- At the input lambda the context is input/apply/step. The subsequent binders
are cap, first, Unit, second, Unit, first result and second result. The selected
closure is passed as a value to the ordinary typed Core apply function. -/
private def closureExpression (stepBody : Expr) (variant : Variant) : Expr :=
  .letE stepBody
    (.letE applyFunction
      (.lambda .word .word
        (.letE (.newCell .word (.apply (.var 2) (.var 0)))
          (.letE (capture 0)
            (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 1)))
              (.letE (secondClosure variant)
                (.letE (.storeCell (.var 3) (.binary .wordAdd (.loadCell (.var 3)) (word 2)))
                  (.letE (.apply (.var 3) (.var 5))
                    (.letE (.apply (.apply (.var 7) (.var 2)) (.binary .wordAdd (.var 6) (word 1)))
                      (.binary .wordAdd
                        (.binary .wordAdd (.binary .wordMul (word 3) (.var 1)) (.var 0))
                        (.loadCell (.var 6))))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (variant : Variant) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := closureExpression step.program.body variant
}

def appliedProgram (step : Aggregates.CheckedDAG) (variant : Variant) (input : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .apply (canonicalProgram step variant).body (.word input)
}

def canonicalNodes (step : Aggregates.CheckedDAG) (variant : Variant) : Nat :=
  programNodes (canonicalProgram step variant)

def appliedNodes (step : Aggregates.CheckedDAG) (variant : Variant) : Nat :=
  programNodes (appliedProgram step variant Word.zero)

/-- Measure actual wrapper syntax with a one-node placeholder. The placeholder
is never admitted as a program; cases check and remeasure their complete step. -/
def appliedOverhead (variant : Variant) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (closureExpression (.word Word.zero) variant) (.word Word.zero)
  } - programNodes {
    resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero
  }

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  variant : Variant
  checked : (canonicalProgram step variant).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.variant

def ofParts? (step : Aggregates.CheckedDAG) (variant : Variant) : Option CheckedPlan :=
  if checked : (canonicalProgram step variant).check = true then
    some ⟨step, variant, checked⟩
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

def instantiate (plan : CheckedPlan) (input : Word) : Program :=
  appliedProgram plan.step plan.variant input

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
end Solcore.Synthesis.Core.Closure
