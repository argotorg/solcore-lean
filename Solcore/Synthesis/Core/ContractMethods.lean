import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.CheckedCoreContract

/-! A contract with two to four external methods over shared storage, behind
the pinned std's dispatcher. The contract binds one checked aggregate step per
method and reads the calldata size. Calldata shorter than four bytes reaches
the default fallback (`0x4924aef0`). Otherwise the selector Word is compared
with each method's selector in declaration order, as std's `RunDispatch`
compares the method tuple the compiler builds in that order, and the first
match runs; no match reaches the fallback too. The matched method's `do_exec`
requires `4 + 32k` bytes for its `k` Word arguments (`0x08638556`), reads them,
and runs its protocol: its input is the wrapping sum of its arguments; slot
zero becomes the method's step of the input plus slot zero, slot one counts the
calls, slot `2 + i` keeps method `i`'s accumulator, and the result is the sum
of slots zero, one and `2 + i`. An odd input reverts with the result. A
rejection reverts with the error selector as its Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.ContractMethods

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch

def version : String := "core-methods-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def minMethods : Nat := 2
def maxMethods : Nat := 4
def maxArity : Nat := 2

/-- Slot zero holds the shared accumulator, slot one the shared call count and
slot `2 + i` method `i`'s accumulator. -/
def resultSlot (position : Nat) : Nat := 2 + position
def slotCount : Nat := 2 + maxMethods

/-- What dispatch needs of a method: its selector and its Word arity. -/
structure Shape where
  selector : Nat
  arity : Nat
  deriving BEq, Repr

/-- The binder at position `position`, counted from the outermost, seen from a
frame of `locals` binders. -/
private def binder (locals position : Nat) : Expr := .var (locals - 1 - position)

/-- The wrapping sum of a method's Word arguments, read at bytes `4 + 32j`. -/
private def input (arity locals : Nat) : Expr :=
  (List.range arity).foldl (fun total index => add total (readAt locals (word (4 + 32 * index)))) (word 0)

/-- Method `position` in the frame of the `methods` steps, the size and the
selector Word: the head check, then the protocol. -/
private def method (methods position arity : Nat) : Expr :=
  let locals := methods + 2
  .ifE (gt (word (4 + 32 * arity)) (binder locals methods)) (reject truncatedError)
    (.letE (input arity locals)
      (.letE (host 0 (locals + 1) (word 0))
        (.letE (.apply (binder (locals + 2) position) (add (.var 1) (.var 0)))
          (.letE (host 1 (locals + 3) (.pair (word 0) (.var 0)))
            (.letE (host 1 (locals + 4) (.pair (word 1) (add (host 0 (locals + 4) (word 1)) (word 1))))
              (.letE (host 1 (locals + 5) (.pair (word (resultSlot position)) (.var 2)))
                (.letE (add (add (host 0 (locals + 6) (word 0)) (host 0 (locals + 6) (word 1)))
                    (host 0 (locals + 6) (word (resultSlot position))))
                  (.ifE (.binary .wordEq (.binary .wordAnd (.var 6) (word 1)) (word 1))
                    (.inRight .word (.inLeft .word (.var 0)))
                    (.inLeft (.sum .word .word) (.var 0))))))))))

/-- Compare the selector Word (local zero) with each remaining method's
selector in declaration order; the first match runs and no match is rejected. -/
private def dispatch (methods : Nat) : List (Nat × Shape) → Expr
  | [] => reject noSelectorError
  | (position, shape) :: rest =>
      .ifE (.binary .wordEq (.var 0) (word shape.selector)) (method methods position shape.arity)
        (dispatch methods rest)

/-- The steps, each bound in turn, the size, std's short-calldata check, the
selector Word and the dispatch. -/
private def contractExpressionWith (shapes : List Shape) (steps : List Expr) : Expr :=
  let methods := steps.length
  steps.foldr (fun step body => .letE step body)
    (.letE (host 7 methods .unit)
      (.ifE (gt (word 4) (.var 0)) (reject noSelectorError)
        (.letE (selectorWord (methods + 1))
          (dispatch methods (shapes.zipIdx.map fun (shape, position) => (position, shape))))))

def canonicalProgram (shapes : List Shape) (steps : List Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpressionWith shapes (steps.map (·.program.body))
}

/-- Syntax-only overhead of the wrapper with one placeholder step per shape; the
placeholders are never admitted or run. -/
def overheadWith (shapes : List Shape) : Nat :=
  let wrapper : Program :=
    {resultType := resultType, dataDefinitions := [], body := contractExpressionWith shapes (shapes.map (fun _ => word 0))}
  let placeholder : Program := {resultType := .function .word .word, dataDefinitions := [], body := word 0}
  programNodes wrapper - shapes.length * programNodes placeholder

/-- The dispatch shell without methods, which lies inside the step budget. -/
def programOverhead : Nat := overheadWith []

/-- The selector comparisons, head checks and protocols of the methods, which
lie outside the step budget. -/
def guardNodes (shapes : List Shape) : Nat := overheadWith shapes - programOverhead

/-- The largest guard, four methods of two arguments. -/
def maxGuardNodes : Nat := guardNodes (List.replicate maxMethods ⟨0, maxArity⟩)

structure CheckedPlan where private mk ::
  shapes : List Shape
  steps : List Aggregates.CheckedDAG
  checked : (canonicalProgram shapes steps).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.shapes plan.steps

def ofParts? (shapes : List Shape) (steps : List Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram shapes steps).check = true then some ⟨shapes, steps, checked⟩ else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.ContractMethods
