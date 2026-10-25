import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program

/-! A checked monomorphic reference for a single polymorphic source selector.
The independent step closure is evaluated once. Both candidate computations run
left-to-right before selection; the fixed wrapper exposes the chosen Word,
product fields or sum constructor through a Word result. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.Generic

open Solcore.Core (Word)
open Solcore.Core.Wire

def version : String := "core-generic-selection-plan-v1"

inductive Variant where
  | word
  | pair
  | sum
  deriving Repr, BEq, DecidableEq

namespace Variant

def all : List Variant := [.word, .pair, .sum]

def name : Variant → String
  | .word => "word"
  | .pair => "pair"
  | .sum => "sum"

def ofString? : String → Option Variant
  | "word" => some .word
  | "pair" => some .pair
  | "sum" => some .sum
  | _ => none

def payloadType : Variant → Ty
  | .word => .word
  | .pair => .product .word .word
  | .sum => .sum .word .word

end Variant

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- The generic source definition becomes this ordinary typed Core closure.
Its three curried parameters are flag, left and right, in that order. -/
private def selector (type : Ty) : Expr :=
  .lambda .bool (.function type (.function type type))
    (.lambda type (.function type type)
      (.lambda type type (.ifE (.var 2) (.var 1) (.var 0))))

private def leftCandidate : Variant → Expr
  | .word => .var 3
  | .pair => .pair (.var 3) (.var 4)
  | .sum => .inLeft .word (.var 3)

private def rightCandidate : Variant → Expr
  | .word => .var 2
  | .pair => .pair (.var 2) (.var 3)
  | .sum => .inRight .word (.var 2)

private def result : Variant → Expr
  | .word => .var 0
  | .pair => .binary .wordAdd (.first (.var 0)) (.second (.var 0))
  | .sum => .caseE (.var 0) (.var 0) (.binary .wordAdd (.var 0) (word 1))

/-- At the entry lambda, input/select/step occupy indices 0/1/2. Each
initializer below adds its binder: left Word, input+1, right Word, flag,
left candidate, right candidate and selected value. -/
private def genericExpression (stepBody : Expr) (variant : Variant) : Expr :=
  .letE stepBody
    (.letE (selector variant.payloadType)
      (.lambda .word .word
        (.letE (.apply (.var 2) (.var 0))
          (.letE (.binary .wordAdd (.var 1) (word 1))
            (.letE (.apply (.var 4) (.var 0))
              (.letE (.binary .wordEq (.binary .wordAnd (.var 3) (word 1)) (word 1))
                (.letE (leftCandidate variant)
                  (.letE (rightCandidate variant)
                    (.letE (.apply (.apply (.apply (.var 7) (.var 2)) (.var 1)) (.var 0))
                      (result variant))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (variant : Variant) : Program := {
  resultType := .function .word .word
  dataDefinitions := []
  body := genericExpression step.program.body variant
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

/-- The placeholder measures syntax only. Admission still checks the complete
original program, and callers remeasure it after step generation. -/
def appliedOverhead (variant : Variant) : Nat :=
  programNodes {
    resultType := .word, dataDefinitions := [],
    body := .apply (genericExpression (.word Word.zero) variant) (.word Word.zero)
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
end Solcore.Synthesis.Core.Generic
