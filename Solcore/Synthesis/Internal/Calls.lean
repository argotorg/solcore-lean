import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Synthesis.Core.StdDispatch
import Solcore.Synthesis.Internal.Storage
import Solcore.ContractRuntime.Internal.BalancedLaws
import Solcore.Synthesis.Stateful.Sequence
import Solcore.ContractRuntime.Internal.NestedLaws
import Solcore.Abi.Keccak256

/-!
# Profiles: calls and methods

The profiles `stateful-calls`, `stateful-call-value`, `stateful-forwarded-value` and
`stateful-methods`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.CallValue
/-! A checked call-value protocol around a closed aggregate step. The ABI
supplies a flags Word and an input Word; the `callValue` host function supplies
the transaction's value. The contract writes `step(input + value + slot0)` to
slot zero and adds the value to slot one, so slot one is the value the contract
has accepted. The original flags parity then selects return or revert. The
public balanced runtime transfers the value before the root runs and commits or
refunds it together with the working world; the Core expression itself never
reads a balance. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallValue

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-call-value-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- The binder at `position`, counted from the outermost, in a frame with
`depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- After the two Unit write binders, the flags are binder one and the result
binder six. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound 9 1) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (bound 9 6)))
    (.inLeft (.sum .word .word) (bound 9 6))

/-- Every host application names its exact local depth. The binders are the
step, flags, input, value, both slot reads, the result and the two writes;
slot zero is written before slot one. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 4 3 .unit)
          (.letE (host 0 4 (word 0))
            (.letE (host 0 5 (word 1))
              (.letE (.apply (bound 6 0) (.binary .wordAdd (.binary .wordAdd (bound 6 2) (bound 6 3)) (bound 6 4)))
                (.letE (host 1 7 (.pair (word 0) (bound 7 6)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (bound 8 5) (bound 8 3))))
                    completion))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead measurement; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The checked step and the value the contract holds after deployment. The
deployment value is part of the deployed world, not of the Core program. -/
structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  deploymentValue : Word
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) (deploymentValue : Word) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, deploymentValue, checked⟩ else none

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
end Solcore.Synthesis.Core.CallValue
end

section
-- leanmerge: from Solcore.Synthesis.Core.ContractMethods
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.ForwardedCall
/-! Two checked host contracts for one value-forwarding Word call. The parent
adds its input and call value to slot zero, calls the child with an explicit
amount, records the child's typed outcome and selects a root return or revert.
The child folds its own call value into a closed aggregate step and records the
value it accepted. Account transfers, child rollback and root rollback belong
to the balanced top-level runtime and its nested scheduler. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.ForwardedCall

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-forwarded-value-call-v1"
def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)
private def bitSet (input : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd input (word bit)) (word bit)
private def returned (payload : Expr) : Expr := .inLeft (.sum .word .word) payload
private def reverted (payload : Expr) : Expr := .inRight .word (.inLeft .word payload)
private def trapped (reason : Expr) : Expr := .inRight .word (.inRight .word reason)

/-- Collapse the four call outcomes to an adjusted payload or a trap reason.
Each case introduces its own payload binder; no parent local is used here. -/
private def consumeChild (call : Expr) : Expr :=
  .caseE call (.inLeft .word (.var 0))
    (.caseE (.var 0) (.inLeft .word (.binary .wordAdd (.var 0) (word 1)))
      (.caseE (.var 0) (.inRight .word (.var 0)) (.inRight .word (.var 0))))

/-- Successful child-outcome decoding adds a payload binder above seven parent
locals; the original input is then local eight, after the result binding. -/
private def finishParent : Expr :=
  .letE (host 1 8 (.pair (word 1) (.var 0)))
    (.letE (.binary .wordAdd (host 0 9 (word 0)) (host 0 9 (word 1)))
      (.ifE (bitSet (.var 8) 2) (reverted (.var 0)) (returned (.var 0))))

/-- The target, input and amount Words follow the selector; the call value is
read through the host. The child receives the input Word and value `amount`. -/
private def parentExpression : Expr :=
  .letE (readInput 0 4)
    (.letE (readInput 1 36)
      (.letE (readInput 2 68)
        (.letE (host 4 3 .unit)
          (.letE (.binary .wordAdd (.binary .wordAdd (host 0 4 (word 0)) (.var 2)) (.var 0))
            (.letE (host 1 5 (.pair (word 0) (.var 0)))
              (.letE (consumeChild (host 11 6 (.pair (.var 5) (.pair (.var 3) (.var 4)))))
                (.caseE (.var 0) finishParent (trapped (.var 0)))))))))

private def childExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 0)
      (.letE (host 4 2 .unit)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 1))
            (.letE (.apply (.var 4) (.binary .wordAdd (.binary .wordAdd (.var 3) (.var 2)) (.var 1)))
              (.letE (host 1 6 (.pair (word 0) (.var 0)))
                (.letE (host 1 7 (.pair (word 1) (.binary .wordAdd (.var 2) (.var 4))))
                  (.ifE (bitSet (.var 6) 1) (reverted (.var 2)) (returned (.var 2))))))))))

def canonicalParentProgram : Program := {
  resultType := resultType, dataDefinitions := [], body := parentExpression }

def canonicalChildProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType, dataDefinitions := [], body := childExpression step.program.body }

def combinedNodes (step : Aggregates.CheckedDAG) : Nat :=
  programNodes canonicalParentProgram + programNodes (canonicalChildProgram step)

/-- Both wrappers, with the child step counted once. The dummy expression only
measures syntax and is never checked or executed as a contract. -/
def programOverhead : Nat :=
  programNodes canonicalParentProgram +
    programNodes {resultType := resultType, dataDefinitions := [], body := childExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  parentChecked : canonicalParentProgram.check = true
  childChecked : (canonicalChildProgram step).check = true

namespace CheckedPlan

def parentProgram (_plan : CheckedPlan) : Program := canonicalParentProgram
def childProgram (plan : CheckedPlan) : Program := canonicalChildProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if parentChecked : canonicalParentProgram.check = true then
    if childChecked : (canonicalChildProgram step).check = true then
      some ⟨step, parentChecked, childChecked⟩
    else none
  else none

theorem parentWellTyped (plan : CheckedPlan) : plan.parentProgram.WellTyped :=
  Program.check_full_sound plan.parentChecked
theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

def parentCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.parentProgram.toCore, Program.check_promotes_current plan.parentChecked⟩
def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def parentContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.parentCode rfl
def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.childCode rfl

theorem parentContract_program (plan : CheckedPlan) :
    plan.parentContract.code.program = plan.parentProgram.toCore := rfl
theorem childContract_program (plan : CheckedPlan) :
    plan.childContract.code.program = plan.childProgram.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.ForwardedCall
end

section
-- leanmerge: from Solcore.Synthesis.Core.NestedCall
/-! Two checked host contracts for one value-bearing Word call. The parent
records its pre-call write, consumes the child's typed outcome, and selects a
root return/revert. The child owns a closed aggregate step. Account transfer,
child rollback, root rollback and log commitment belong to the nested runtime. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.NestedCall

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-nested-word-call-v1"
def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)
private def bitSet (input : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd input (word bit)) (word bit)
private def returned (payload : Expr) : Expr := .inLeft (.sum .word .word) payload
private def reverted (payload : Expr) : Expr := .inRight .word (.inLeft .word payload)
private def trapped (reason : Expr) : Expr := .inRight .word (.inRight .word reason)

/-- Collapse the four call outcomes to an adjusted payload or a trap reason.
Each case introduces its own payload binder; no parent local is used here. -/
private def consumeChild (call : Expr) : Expr :=
  .caseE call (.inLeft .word (.var 0))
    (.caseE (.var 0) (.inLeft .word (.binary .wordAdd (.var 0) (word 1)))
      (.caseE (.var 0) (.inRight .word (.var 0)) (.inRight .word (.var 0))))

/-- Successful child-outcome decoding adds a payload binder above eight parent
locals. Both Unit binders below remain present when reading the original input. -/
private def finishParent : Expr :=
  .letE (host 1 9 (.pair (word 1) (.var 0)))
    (.letE (host 13 10 (.pair (word 3) (.var 1)))
      (.letE (.binary .wordAdd (host 0 11 (word 0)) (host 0 11 (word 1)))
        (.ifE (bitSet (.var 10) 2) (reverted (.var 0)) (returned (.var 0)))))

private def parentExpression : Expr :=
  .letE (readInput 0 4)
    (.letE (readInput 1 36)
      (.letE (host 0 2 (word 0))
        (.letE (.binary .wordAdd (.var 0) (.var 1))
          (.letE (host 1 4 (.pair (word 0) (.var 0)))
            (.letE (host 13 5 (.pair (word 1) (.var 1)))
              (.letE (.ifE (bitSet (.var 4) 4) (word 1) (word 0))
                (.letE (consumeChild (host 11 7 (.pair (.var 6) (.pair (.var 0) (.var 5)))))
                  (.caseE (.var 0) finishParent (trapped (.var 0))))))))))

private def childExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 0)
      (.letE (host 0 2 (word 0))
        (.letE (host 0 3 (word 1))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (host 1 5 (.pair (word 0) (.var 0)))
              (.letE (host 1 6 (.pair (word 1) (.binary .wordAdd (.var 2) (word 1))))
                (.letE (host 13 7 (.pair (word 2) (.var 2)))
                  (.ifE (bitSet (.var 6) 1) (reverted (.var 3)) (returned (.var 3))))))))))

def canonicalParentProgram : Program := {
  resultType := resultType, dataDefinitions := [], body := parentExpression }

def canonicalChildProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType, dataDefinitions := [], body := childExpression step.program.body }

def combinedNodes (step : Aggregates.CheckedDAG) : Nat :=
  programNodes canonicalParentProgram + programNodes (canonicalChildProgram step)

/-- Both wrappers, with the child step counted once. The dummy expression only
measures syntax and is never checked or executed as a contract. -/
def programOverhead : Nat :=
  programNodes canonicalParentProgram +
    programNodes {resultType := resultType, dataDefinitions := [], body := childExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  parentChecked : canonicalParentProgram.check = true
  childChecked : (canonicalChildProgram step).check = true

namespace CheckedPlan

def parentProgram (_plan : CheckedPlan) : Program := canonicalParentProgram
def childProgram (plan : CheckedPlan) : Program := canonicalChildProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if parentChecked : canonicalParentProgram.check = true then
    if childChecked : (canonicalChildProgram step).check = true then
      some ⟨step, parentChecked, childChecked⟩
    else none
  else none

abbrev ofParts? := ofStep?

theorem parentWellTyped (plan : CheckedPlan) : plan.parentProgram.WellTyped :=
  Program.check_full_sound plan.parentChecked
theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

def parentCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.parentProgram.toCore, Program.check_promotes_current plan.parentChecked⟩
def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def parentContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.parentCode rfl
def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.childCode rfl

theorem parentContract_program (plan : CheckedPlan) :
    plan.parentContract.code.program = plan.parentProgram.toCore := rfl
theorem childContract_program (plan : CheckedPlan) :
    plan.childContract.code.program = plan.childProgram.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.NestedCall
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallValueEmitter
/-! Emit the fixed call-value protocol. The constructor and `run` are payable,
so the dispatcher never rejects value. `run` reads the value with the pinned
`std.opcodes` wrapper `callvalue`, writes `step(input + value + slot0)` to slot
zero and adds the value to slot one, in the same order as the original Core
contract. Odd flags revert after both writes with the result encoded as exactly
32 bytes; even flags return it through the ABI. Memory at zero is touched only
before the terminal revert. The arbitrary checked aggregate entry is preserved. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallValue

open Solcore.Synthesis.Core.CallValue (CheckedPlan)

def emitterVersion : String := "solcore-source-call-value-v1"
def wrapperVersion : String := "solcore-word-call-value-contract-v1"
def contractName : String := "SynthesizedCallValue"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedCallValueDeploy"]
def runtimePath : List String := ["SynthesizedCallValueDeploy", "SynthesizedCallValue"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_", "callvalue as sc_callvalue"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    constructor() payable {}",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public payable returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_value: word = sc_callvalue();",
    "        let sc_old: word = sload(0);",
    "        let sc_total: word = sload(1);",
    "        let sc_result: word = sc_step(sc_input + sc_value + sc_old);",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_total + sc_value);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.CallValue
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.CallValueExecution
/-! Execute the original checked call-value contract over a persistent account
world with the public balanced runtime. Each invocation transfers its value from
the caller to the contract before the root runs, starts a fresh Core heap and
journal, and only the terminal `finalWorld` becomes the next transaction's
world. A revert or trap selects the pre-transfer checkpoint, so the value is
refunded by `ContractRuntime`, not by this observer. Observations report slots
zero and one and the contract's committed balance; the caller's balance is
never reported. A rejected transfer is reported as such, never as a revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallValueExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallValue (CheckedPlan)

def historySchema : String := "solcore-lean.call-value-history.v2"

/-- One caller and one installed contract, as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  value : Word
  deriving BEq

/-- The caller's funds in the declared post-deployment world. -/
def callerFunds : Nat := 2 ^ 80

/-- The selector of `run(uint256,uint256)`, followed by the flags and the input
as two big-endian Words. The value travels with the invocation, not the data. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the step result and slot one the accepted value. -/
def observedSlots : List Word := [Word.ofNatModulo 0, Word.ofNatModulo 1]

/-- The world after an empty payable constructor received `deploymentValue`. -/
def initialWorldForContract (contract : CheckedCoreContract) (deploymentValue : Word)
    (bindings : Bindings) : WorldState :=
  (WorldState.empty.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo callerFunds))).putAccount
    bindings.address ((Account.empty.withCode contract.code).withBalance deploymentValue)

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account observedSlots
  | none => Json.null

private def worldBalance (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => toJson (toString account.balance.val)
  | none => Json.null

private def committed (world : WorldState) (bindings : Bindings) : List (String × Json) :=
  [("committedStorage", worldStorage world bindings), ("committedBalance", worldBalance world bindings),
   ("accountStorage", AccountStorage.contractJson world bindings.address)]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. -/
def observeContract (contract : CheckedCoreContract) (deploymentValue : Word)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := initialWorldForContract contract deploymentValue bindings
  let initial := world
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := transaction.value, inputData := inputData transaction.flags transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure")] ++ committed prior bindings))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (BalancedTopLevelExecution.run resolved invocation installed registry fuel).view with
          | .rejected rejected =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "transfer-rejected"),
                ("detail", toJson (reprStr rejected.failure))] ++ committed prior bindings))
              stopped := some transaction.id
          | .execution execution =>
              match execution.view with
              | .completed terminal =>
                  world := terminal.finalWorld
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ committed world bindings))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .outOfFuel _ _ _ =>
                  rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel")] ++ committed prior bindings))
                  stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson observedSlots),
    ("deploymentValue", toJson (toString deploymentValue.val)),
    ("initialStorage", worldStorage initial bindings),
    ("initialAccountStorage", AccountStorage.contractJson initial bindings.address),
    ("initialBalance", worldBalance initial bindings),
    ("initialLogs", toJson ([] : List Json)), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("finalBalance", worldBalance world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract plan.deploymentValue transactions bindings fuel

end Solcore.Synthesis.Stateful.CallValueExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.CallValueCases
/-! Call-value cases retain one original host-aware Core contract, the value it
holds after deployment and an ordered history of `(flags, input, value)`
transactions. Values are bounded so that the funded local sender can always pay
them. Saved outputs and balances are never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallValue
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Stateful.CallValueExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-call-value-case.v1"
def planSchema : String := "solcore-lean.call-value-plan.v1"
def profileVersion : String := "stateful-call-value-v1/value-sequence-seed-v2"
def templateVersion : String := "slot-step-value-total-revert-odd-flags-v1"
def valueCorpusSchema : String := "solcore-lean.semantic-call-value-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Call values: zero, small values, both sides of the 64-bit boundary and a
large value the funded local sender can still pay three times. -/
def valueBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1),
    Word.ofNatModulo (2 ^ 64), Word.ofNatModulo (2 ^ 70)]

def deploymentBank : List Word := [Word.zero, Word.ofNatModulo 5]

/-- Every single value, including the deployment value, and the total a
scenario sends are bounded by the local sender's funds. -/
def maxValue : Nat := 2 ^ 70
def maxTotal : Nat := 2 ^ 72

def totalValue (deploymentValue : Word) (transactions : List Transaction) : Nat :=
  transactions.foldl (fun total tx => total + tx.value.val) deploymentValue.val

def validTransactions (deploymentValue : Word) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.value.val ≤ maxValue) = true ∧
    totalValue deploymentValue transactions ≤ maxTotal

instance (deploymentValue : Word) (transactions : List Transaction) :
    Decidable (validTransactions deploymentValue transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.deploymentValue transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.deploymentValue transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical call-value contract exceeds the 512-node case limit"
  else throw s!"call-value scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, values of at most 2^70 and at most 2^72 in total"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("value", toJson (toString tx.value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.CallValueExecution.calldata tx.flags tx.input))]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction :=
      ⟨← row.getObjValAs? String "id", ← wordField row "flags", ← wordField row "input", ← wordField row "value"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, value or calldata"
    return transaction
  unless decide ((transactions.map (·.id)).Nodup) && transactions.all (fun tx => Storage.validId tx.id) do
    throw "call-value scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("deploymentValue", toJson (toString plan.deploymentValue.val))]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call-value plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let deploymentValue ← wordField json "deploymentValue"
  unless deploymentValue.val ≤ maxValue do throw "deployment value exceeds 2^70"
  let some plan := CheckedPlan.ofParts? step deploymentValue | throw "call-value contract failed full host-Core admission"
  unless json == planJson plan do throw "call-value plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "call-value contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson Solcore.Synthesis.Stateful.CallValueExecution.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("callValuePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.CallValue.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call-value case schema"
  let plan ← checkedPlan (← json.getObjVal? "callValuePlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical call-value plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed slots must be zero and one"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.CallValueExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- A separate stream keeps sequence choices independent of the step seed's
helper-count and template digits. Each choice uses the high half of one draw:
the low bits of a power-of-two LCG have short periods. The draws are three
inputs, three values, the deployment value and the completion pattern. The
stream starts at SplitMix64's finalizer of the seed xor its domain, so that
consecutive seeds' choices do not step by a fixed residue. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x76616c75652d7478))
  let mut values : Array Nat := #[]
  for bound in [6, 6, 6, 6, 6, 6, 2, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 7 0) [false, false, false]

def generatedDeploymentValue (seed : Seed) : Word :=
  deploymentBank.getD ((sequenceChoices seed).getD 6 0) Word.zero

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityFlags odd, boundaryInputs.getD (choices.getD index 0) Word.zero,
      valueBank.getD (choices.getD (3 + index) 0) Word.zero⟩

/-- Keep the total sent, with the deployment value, within `maxTotal`: a value
that would exceed it is zero. Three transactions never reach the total. -/
def boundedValues (deploymentValue : Word) (transactions : List Transaction) : List Transaction :=
  (transactions.foldl (fun (total, result) tx =>
      if total + tx.value.val ≤ maxTotal then (total + tx.value.val, result ++ [tx])
      else (total, result ++ [{tx with value := Word.zero}]))
    (deploymentValue.val, [])).2

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  boundedValues (generatedDeploymentValue seed) (Stateful.Sequence.blocks blockTransactions seed count)

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.CallValue.programOverhead < nodes do
    throw "node budget is too small for the call-value wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.CallValue.programOverhead) revision
  let some plan := CheckedPlan.ofParts? step (generatedDeploymentValue seed) |
    throw "generated call-value plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "call-value contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-value-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : String) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some slot) |
    throw "committed slot missing"
  decimal entry "value"

/-- Original Core must complete every transaction with the prescribed
completion; each committed balance must be the deployment value plus slot one,
and a revert must keep the prior slots and balance. -/
def checkBalances (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "call-value history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "call-value history length changed"
  let deployment := scenario.plan.deploymentValue.val
  unless (← decimal history "initialBalance") == deployment && (← slotValue history "1" "initialStorage") == 0 do
    throw "call-value deployment does not hold exactly its deployment value"
  let mut statuses : List String := []
  let mut priorBalance := deployment
  let mut priorStorage ← history.getObjVal? "initialStorage"
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "call-value history did not follow its flags parities"
    let balance ← decimal row "committedBalance"
    unless balance == (deployment + (← slotValue row "1")) % 2 ^ 256 do
      throw "committed balance differs from the deployment value plus accepted value"
    if status == "reverted" then
      unless balance == priorBalance && (← row.getObjVal? "committedStorage") == priorStorage do
        throw "a reverted call-value transaction changed the committed balance or slots"
    priorBalance := balance
    priorStorage ← row.getObjVal? "committedStorage"
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkBalances scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "call-value history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call-value history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-value-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson valueCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags, inputs, values and the deployment value all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.flags.val + transaction.input.val + transaction.value.val) scenario.plan.deploymentValue.val

/-- Transaction count, complete program size/literals, then runtime flags,
inputs, values and the deployment value. Every axis is a natural number and
the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      valueWeight candidate < valueWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (deploymentValue : Word)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step deploymentValue
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions and a zero deployment value, then per transaction:
removal, bank replacements of the input, smaller bank values, and flags reduced
to their parity or with the revert bit cleared. Candidates still need execution
to preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let deployment := source.plan.deploymentValue
  let mut raw : List (Aggregates.CheckedDAG × Word × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step, deployment,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, deployment, source.transactions)]
  raw := raw ++ [(step, Word.zero, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for input in boundaryInputs do
      raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx => {tx with input := input})]
    for value in valueBank.filter (·.val < transaction.value.val) do
      raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx => {tx with value := value})]
    raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, deploymentValue, transactions) in raw do
    if let some reduced := sealReduction source step deploymentValue transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.CallValue.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from call-value plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from call-value wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-value-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call-value provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.deploymentValue admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported call-value case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson valueCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.CallValue
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedCallEmitter
/-! Emit two contracts with one raw Word call, explicit value, ordered logs and
independent child/root rollback. Scratch buffers reserve memory from the free
pointer before use. Child return data must contain exactly one Word. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedCall

open Solcore.Synthesis.Core.NestedCall (CheckedPlan)

def emitterVersion : String := "solcore-source-nested-call-v2"
def wrapperVersion : String := "solcore-word-nested-call-v1"
def parentContractName : String := "SynthesizedCaller"
def childContractName : String := "SynthesizedCallee"
def parentMethodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def parentConstructorValue : String := "8"
def childConstructorValue : String := "0"
def parentDeployPath : List String := ["SynthesizedCallerDeploy"]
def parentRuntimePath : List String := ["SynthesizedCallerDeploy", "SynthesizedCaller"]
def childDeployPath : List String := ["SynthesizedCalleeDeploy"]
def childRuntimePath : List String := ["SynthesizedCalleeDeploy", "SynthesizedCallee"]

structure EmittedContracts where
  source : String
  parentContractName : String
  childContractName : String
  parentMethodSignature : String
  selector : String
  parentConstructorValue : String
  childConstructorValue : String
  parentDeployPath : List String
  parentRuntimePath : List String
  childDeployPath : List String
  childRuntimePath : List String
  deriving Repr, BEq

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mload", "mstore", "calldataload", "gas", "call",
      "returndatasize", "return_", "revert_", "invalid", "log1 as log1_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ childContractName ++ " {",
    "    fallback() payable {",
    "        let sc_input: word = calldataload(0);",
    "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + 1);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
    "        mstore(sc_ptr, sc_computed);", "        log1_(sc_ptr, 32, 2);",
    "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
    "        return_(sc_ptr, 32);", "    }", "}", "",
    "contract " ++ parentContractName ++ " {",
    "    constructor() payable {}",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_before: word = sload(0) + sc_input;",
    "        sstore(0, sc_before);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
    "        mstore(sc_ptr, sc_before);", "        log1_(sc_ptr, 32, 1);",
    "        let sc_value: word = 0;",
    "        if ((sc_input & 4) == 4) {", "            sc_value = 1;", "        }",
    "        mstore(sc_ptr, sc_input);",
    "        let sc_ok: word = call(gas(), sc_target, sc_value, sc_ptr, 32, sc_ptr + 32, 32);",
    "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
    "        let sc_after: word = mload(sc_ptr + 32);",
    "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
    "        sstore(1, sc_after);",
    "        mstore(sc_ptr, sc_after);", "        log1_(sc_ptr, 32, 3);",
    "        let sc_result: word = sload(0) + sload(1);",
    "        if ((sc_input & 2) == 2) {",
    "            mstore(sc_ptr, sc_result);", "            revert_(sc_ptr, 32);", "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    parentContractName, childContractName, parentMethodSignature, selector,
    parentConstructorValue, childConstructorValue,
    parentDeployPath, parentRuntimePath, childDeployPath, childRuntimePath
  }

end Solcore.Synthesis.Source.NestedCall
end

section
-- leanmerge: from Solcore.Synthesis.Source.ForwardedCallEmitter
/-! Emit a payable parent and a payable child for one value-forwarding raw
Word call. The parent reads its call value through the pinned `callvalue`
wrapper and forwards the explicit amount through the raw `call` wrapper; the
child reads the value it received the same way. Scratch buffers reserve memory
from the free pointer before use, and child return data must contain exactly
one Word. No logs are emitted. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ForwardedCall

open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)

def emitterVersion : String := "solcore-source-forwarded-value-v1"
def wrapperVersion : String := "solcore-word-forwarded-value-v1"
def parentContractName : String := "SynthesizedForwarder"
def childContractName : String := "SynthesizedRecipient"
def parentMethodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
/-- The parent's endowment, 2^72, covers three forwards of the largest bank value. -/
def parentConstructorValue : String := toString (2 ^ 72 : Nat)
def childConstructorValue : String := "0"
def parentDeployPath : List String := ["SynthesizedForwarderDeploy"]
def parentRuntimePath : List String := ["SynthesizedForwarderDeploy", "SynthesizedForwarder"]
def childDeployPath : List String := ["SynthesizedRecipientDeploy"]
def childRuntimePath : List String := ["SynthesizedRecipientDeploy", "SynthesizedRecipient"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mload", "mstore", "calldataload", "gas", "call",
      "returndatasize", "return_", "revert_", "invalid", "callvalue as sc_callvalue"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ childContractName ++ " {",
    "    fallback() payable {",
    "        let sc_input: word = calldataload(0);",
    "        let sc_value: word = sc_callvalue();",
    "        let sc_old0: word = sload(0);", "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_value + sc_old0);",
    "        sstore(0, sc_computed);", "        sstore(1, sc_old1 + sc_value);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 32);",
    "        mstore(sc_ptr, sc_computed);",
    "        if ((sc_input & 1) == 1) {", "            revert_(sc_ptr, 32);", "        }",
    "        return_(sc_ptr, 32);", "    }", "}", "",
    "contract " ++ parentContractName ++ " {",
    "    constructor() payable {}",
    "    function run(target: uint256, input: uint256, amount: uint256) public payable returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_amount: word = Typedef.rep(amount);",
    "        let sc_before: word = sload(0) + sc_input + sc_callvalue();",
    "        sstore(0, sc_before);",
    "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
    "        mstore(sc_ptr, sc_input);",
    "        let sc_ok: word = call(gas(), sc_target, sc_amount, sc_ptr, 32, sc_ptr + 32, 32);",
    "        if (!(returndatasize() == 32)) {", "            invalid();", "        }",
    "        let sc_after: word = mload(sc_ptr + 32);",
    "        if (sc_ok == 0) {", "            sc_after = sc_after + 1;", "        }",
    "        sstore(1, sc_after);",
    "        let sc_result: word = sload(0) + sload(1);",
    "        if ((sc_input & 2) == 2) {",
    "            mstore(sc_ptr, sc_result);", "            revert_(sc_ptr, 32);", "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    parentContractName, childContractName, parentMethodSignature, selector,
    parentConstructorValue, childConstructorValue,
    parentDeployPath, parentRuntimePath, childDeployPath, childRuntimePath
  }

end Solcore.Synthesis.Source.ForwardedCall
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.NestedCallExecution
/-! Original checked-Core execution of a fixed parent/leaf protocol. Only the
public scheduler's committed world and transaction journal leave an invocation.
Exhausted working state and speculative logs are never reported as committed.
Both contracts' whole committed storage is reported with their slots zero and one. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.NestedCallExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)

abbrev Transaction := StorageExecution.Transaction

def historySchema : String := "solcore-lean.call-history.v2"
def bindingsSchema : String := "solcore-lean.call-bindings.v1"

structure Bindings where
  caller : Address
  parent : Address
  child : Address

def fixtureBindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩

def bindingsJson (bindings : Bindings) : Json := Json.mkObj [
  ("schema", toJson bindingsSchema), ("caller", toJson (toString bindings.caller.val)),
  ("parent", toJson (toString bindings.parent.val)), ("child", toJson (toString bindings.child.val))]

private def address (text : String) : Except String Address := do
  unless text.length ≤ 49 do throw "address is too long"
  let some value := text.toNat? | throw "invalid decimal address"
  unless toString value = text do throw "noncanonical decimal address"
  if bounded : value < addressModulus then return ⟨value, bounded⟩
  else throw "address exceeds 160 bits"

def decodeBindings (json : Json) : Except String Bindings := do
  unless (← json.getObjValAs? String "schema") = bindingsSchema do throw "unsupported call bindings schema"
  let result : Bindings := ⟨← address (← json.getObjValAs? String "caller"),
    ← address (← json.getObjValAs? String "parent"), ← address (← json.getObjValAs? String "child")⟩
  unless result.caller != result.parent && result.caller != result.child && result.parent != result.child do
    throw "caller, parent and child must be distinct"
  unless result.parent.val > 17 && result.child.val > 17 &&
      result.parent.val != 256 && result.child.val != 256 do
    throw "contracts must not use precompile addresses"
  unless json == bindingsJson result do throw "bindings differ from their canonical representation"
  return result

/-- Bind the actual child address at execution time, leaving both stored Core
programs and emitted source independent of deployment addresses. -/
def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++
    encodeWordBytesBE (addressToWord bindings.child) ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (bindings : Bindings) (input : Word) : String := encodeBytesText (inputData bindings input).bytes

def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller Account.empty
    |>.putAccount bindings.parent ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo 8))
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

private def accountJson (world : WorldState) (role : String) (address : Address) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", StorageExecution.storageJson account)]

def accountsJson (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent, accountJson world "child" bindings.child]

/-- Both contracts' whole committed storage, in role order. -/
def wholeStorageJson (world : WorldState) (bindings : Bindings) : Json :=
  AccountStorage.worldJson world [("parent", bindings.parent), ("child", bindings.child)]

def logsJson (journal : TransactionJournal) : Json := toJson (journal.logList.map fun entry => Json.mkObj [
  ("address", toJson (toString entry.emitter.val)),
  ("topics", toJson [toString entry.topic.val]),
  ("data", toJson (encodeBytesText (encodeWordBytesBE entry.payload)))])

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Each transaction resolves the root against the current committed world;
the scheduler resolves the child at its actual call boundary. Local heaps and
transaction journals start fresh, while the selected world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.parent then some plan.parentContract
      else if target = bindings.child then some plan.childContract else none }
  let mut world := initialWorld plan bindings
  let initial := accountsJson world bindings
  let initialWhole := wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.parent, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData bindings transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.parent with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure"),
            ("committedAccounts", accountsJson prior bindings), ("accountStorage", wholeStorageJson prior bindings),
            ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (OneLevelNestedExecution.run resolved invocation installed registry fuel).view with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedAccounts", accountsJson world bindings), ("accountStorage", wholeStorageJson world bindings),
                ("logs", logsJson terminal.committedJournal)]))
              match terminal.outcome with
              | .trapped _ => stopped := some transaction.id
              | _ => pure ()
          | .outOfFuel _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel"),
                ("committedAccounts", accountsJson prior bindings), ("accountStorage", wholeStorageJson prior bindings),
            ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson world bindings),
    ("finalAccountStorage", wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

end Solcore.Synthesis.Stateful.NestedCallExecution
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.ForwardedCallExecution
/-! Original checked-Core execution of the fixed value-forwarding parent/child
protocol. Each transaction transfers its call value from the caller to the
parent through the public balanced runtime before the root runs, and the nested
scheduler transfers the forwarded amount at the child call boundary. Only the
terminal committed world and journal leave an invocation: a child revert keeps
its amount with the parent, and a root revert or trap selects the pre-transfer
checkpoint. Neither refund is performed by this observer, and the caller's
balance is never reported. A rejected top-level transfer is reported as such,
never as a revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ForwardedCallExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)

def historySchema : String := "solcore-lean.forward-history.v2"

/-- One caller, the parent and the child, as for the parent/child call profile. -/
abbrev Bindings := NestedCallExecution.Bindings

structure Transaction where
  id : String
  input : Word
  value : Word
  amount : Word
  deriving BEq

/-- The caller's funds and the parent's endowment in the declared
post-deployment world; the child holds nothing. -/
def callerFunds : Nat := 2 ^ 80
def parentEndowment : Nat := 2 ^ 72

/-- The selector of `run(uint256,uint256,uint256)`, the actual child address,
the input and the forwarded amount. The call value travels with the
invocation, not the data. -/
def inputData (bindings : Bindings) (input amount : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x24, 0xb9, 0x12, 0xe5] ++
    encodeWordBytesBE (addressToWord bindings.child) ++ encodeWordBytesBE input ++ encodeWordBytesBE amount
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (bindings : Bindings) (input amount : Word) : String :=
  encodeBytesText (inputData bindings input amount).bytes

def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller (Account.empty.withBalance (Word.ofNatModulo callerFunds))
    |>.putAccount bindings.parent
      ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo parentEndowment))
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Each transaction resolves the root against the current committed world; the
scheduler resolves the child at its actual call boundary. Local heaps and
transaction journals start fresh, while the selected world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.parent then some plan.parentContract
      else if target = bindings.child then some plan.childContract else none }
  let mut world := initialWorld plan bindings
  let initial := NestedCallExecution.accountsJson world bindings
  let initialWhole := NestedCallExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.parent, caller := bindings.caller, callValue := transaction.value,
        inputData := inputData bindings transaction.input transaction.amount }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      let unknown := [("committedAccounts", NestedCallExecution.accountsJson prior bindings),
        ("accountStorage", NestedCallExecution.wholeStorageJson prior bindings), ("logs", Json.null)]
      match registry.resolve? prior bindings.parent with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure")] ++ unknown))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (BalancedTopLevelExecution.run resolved invocation installed registry fuel).view with
          | .rejected rejected =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "transfer-rejected"),
                ("detail", toJson (reprStr rejected.failure))] ++ unknown))
              stopped := some transaction.id
          | .execution execution =>
              match execution.view with
              | .completed terminal =>
                  world := terminal.finalWorld
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedAccounts", NestedCallExecution.accountsJson world bindings),
                    ("accountStorage", NestedCallExecution.wholeStorageJson world bindings),
                    ("logs", NestedCallExecution.logsJson terminal.committedJournal)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .outOfFuel _ _ _ =>
                  rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel")] ++ unknown))
                  stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", NestedCallExecution.accountsJson world bindings),
    ("finalAccountStorage", NestedCallExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

end Solcore.Synthesis.Stateful.ForwardedCallExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.ForwardedCallCases
/-! A forwarded-value case retains two original checked HostWire contracts and
a role-based sequence of `(input, value, amount)` transactions: the call value
the sender pays the parent and the amount the parent forwards to the child.
Every replay reconstructs both programs from the checked step. Saved outcomes
are never an oracle; the public balanced runtime and its nested scheduler
select committed worlds. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ForwardedCall
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.ForwardedCallExecution (Transaction Bindings parentEndowment)
open Solcore.Synthesis.Source.NestedCall (EmittedContracts)

def caseSchema : String := "solcore-lean.semantic-forward-case.v1"
def planSchema : String := "solcore-lean.forward-plan.v1"
def profileVersion : String := "stateful-forwarded-value-v1/forward-sequence-seed-v2"
def templateVersion : String := "forward-value-two-account-call-v1"
def forwardCorpusSchema : String := "solcore-lean.semantic-forward-corpus.v1"

/-- The parent/child call profile's inputs: zero to seven, the maximum and the
high bit. -/
def boundaryInputs : List Word :=
  (List.range 8).map Word.ofNatModulo ++ [Word.maximum, Word.ofNatModulo (2 ^ 255)]

/-- Call values and forwarded amounts: the call-value bank of zero, small
values, both sides of the 64-bit boundary and a value the endowment can
forward three times. -/
def valueBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1),
    Word.ofNatModulo (2 ^ 64), Word.ofNatModulo (2 ^ 70)]

def maxValue : Nat := 2 ^ 70

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.value.val ≤ maxValue && tx.amount.val ≤ maxValue) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : ForwardedCall.combinedNodes plan.step ≤ 512

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", Wire.encodeProgram plan.parentProgram), ("child", Wire.encodeProgram plan.childProgram)]

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : ForwardedCall.combinedNodes plan.step ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical forwarded-value contracts exceed the 512-node case limit"
  else throw s!"forwarded-value scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and values and amounts of at most 2^70"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson (toString tx.value.val)), ("amount", toJson (toString tx.amount.val)),
  ("target", toJson "parent"), ("callee", toJson "child")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "input",
      ← wordField row "value", ← wordField row "amount"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, input, value, amount or role metadata"
    return transaction
  unless validTransactions transactions do
    throw "forwarded-value scenario requires distinct valid transaction IDs and values and amounts of at most 2^70"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported forwarded-value plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "forwarded-value contracts failed full host-Core admission"
  unless json == planJson plan do throw "forwarded-value plan differs from its canonical checked representation"
  unless ForwardedCall.combinedNodes plan.step ≤ 512 do throw "forwarded-value contracts exceed the 512-node case limit"
  return plan

def contractsJson (emitted : EmittedContracts) : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson emitted.parentContractName), ("method", toJson "run"),
    ("signature", toJson emitted.parentMethodSignature), ("selector", toJson emitted.selector),
    ("payable", toJson true), ("deployPath", toJson emitted.parentDeployPath),
    ("runtimePath", toJson emitted.parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.parentConstructorValue)]),
  ("child", Json.mkObj [("name", toJson emitted.childContractName), ("entry", toJson "fallback"),
    ("payable", toJson true), ("inputBytes", toJson (32 : Nat)),
    ("deployPath", toJson emitted.childDeployPath), ("runtimePath", toJson emitted.childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.childConstructorValue)])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson (toString parentEndowment)),
      ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson (toString Solcore.Synthesis.Stateful.ForwardedCallExecution.callerFunds))]

abbrev observedSlotsJson := Storage.observedSlotsJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("forwardPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson ForwardedCall.version), ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", contractsJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. An arbitrary well-typed program is not an admissible
replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic forwarded-value case schema"
  let plan ← checkedPlan (← json.getObjVal? "forwardPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  for name in ["parent", "child"] do
    let program ← (Wire.decodeProgramWithBudget
      {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
      (← originals.getObjVal? name)).mapError (fun
        | .protocol error => error.toJson.compress
        | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
    let expected := if name == "parent" then plan.parentProgram else plan.childProgram
    unless Wire.encodeProgram program == Wire.encodeProgram expected do
      throw "saved original Core program differs from its canonical forwarded-value plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do
    throw "initial accounts differ from the fixed endowment, caller funds and empty storage"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.ForwardedCallExecution.observe scenario.plan scenario.transactions bindings fuel

def childReverts (tx : Transaction) : Bool := tx.input.val % 2 == 1
def rootReverts (tx : Transaction) : Bool := tx.input.val / 2 % 2 == 1

/-- Three inputs, three call modes, three call values and three amounts. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. The stream starts at SplitMix64's finalizer
of the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def sequenceBounds : List Nat := [10, 10, 10, 4, 4, 4, 6, 6, 6, 6, 6, 6]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x666f72776172642d))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- A bank input whose low two bits are replaced by the call mode: bit one
makes the child revert and bit two the root. -/
def modeInput (input : Word) (mode : Nat) : Word :=
  (input.bitAnd (Word.ofNatModulo 3).bitNot).bitOr (Word.ofNatModulo mode)

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (List.range 3).map fun index =>
    ⟨"tx-" ++ toString (first + index),
      modeInput (boundaryInputs.getD (choices.getD index 0) Word.zero) (choices.getD (3 + index) 0),
      valueBank.getD (choices.getD (6 + index) 0) Word.zero, valueBank.getD (choices.getD (9 + index) 0) Word.zero⟩

/-- Keep the forwarded amounts within the parent's endowment in total, so the
parent can always pay: an amount that would exceed it is zero. Three
transactions never reach the endowment. -/
def boundedAmounts (transactions : List Transaction) : List Transaction :=
  (transactions.foldl (fun (total, result) tx =>
      if total + tx.amount.val ≤ parentEndowment then (total + tx.amount.val, result ++ [tx])
      else (total, result ++ [{tx with amount := Word.zero}]))
    (0, [])).2

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  boundedAmounts (Stateful.Sequence.blocks blockTransactions seed count)

private def statusName (reverted : Bool) : String := if reverted then "reverted" else "returned"

/-- Reserve the measured host wrappers before generating the independent step;
the complete contracts are remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && ForwardedCall.programOverhead < nodes do
    throw "node budget is too small for the forwarded-value wrappers or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - ForwardedCall.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated forwarded-value plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless ForwardedCall.combinedNodes scenario.plan.step ≤ nodes do
    throw "forwarded-value contracts exceed their requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "forward-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map fun tx => statusName (rootReverts tx)))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

/-- One account's committed balance and slots zero and one. -/
private def accountValues (accounts : Json) (role : String) : Except String (Nat × Nat × Nat) := do
  let rows ← accounts.getArr?
  let some account := rows.find? (fun row => (row.getObjValAs? String "role").toOption == some role) |
    throw ("committed " ++ role ++ " account missing")
  let slots ← account.getObjValAs? (List Json) "storage"
  let slot := fun (name : String) => do
    let some entry := slots.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some name) |
      throw ("committed " ++ role ++ " slot missing")
    decimal entry "value"
  return (← decimal account "balance", ← slot "0", ← slot "1")

/-- Original Core must complete every transaction with the prescribed root
completion and no logs. A root revert keeps both accounts; a child revert under
a committed root keeps the child's account. In every committed state the child
holds exactly its slot one, and both balances sum to the endowment plus every
committed call value. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "forwarded-value history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "forwarded-value history length changed"
  let mut prior ← history.getObjVal? "initialAccounts"
  unless (← accountValues prior "parent") == (parentEndowment, 0, 0) && (← accountValues prior "child") == (0, 0, 0) do
    throw "forwarded-value deployment does not hold exactly the endowment and empty storage"
  let mut accepted := 0
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (rootReverts tx) do throw "forwarded-value history did not follow its root parity"
    unless (← row.getObjVal? "logs") == toJson ([] : List Json) do throw "a forwarded-value transaction committed logs"
    let accounts ← row.getObjVal? "committedAccounts"
    if status == "reverted" then
      unless accounts == prior do throw "a reverted root changed a committed account"
    else
      if childReverts tx then
        unless (← accountValues accounts "child") == (← accountValues prior "child") do
          throw "a child revert changed the child's committed account"
      accepted := accepted + tx.value.val
    let (parentBalance, _, _) ← accountValues accounts "parent"
    let (childBalance, _, childAccepted) ← accountValues accounts "child"
    unless childBalance == childAccepted && parentBalance + childBalance == parentEndowment + accepted do
      throw "committed balances differ from the forwarded and accepted values"
    prior := accounts
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (rootReverts tx)) do
    throw "forwarded-value history did not follow its prescribed root parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "forwarded-value history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "forwarded-value-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson forwardCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Inputs, call values and amounts all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.input.val + transaction.value.val + transaction.amount.val) 0

/-- Both original programs, as for the parent/child call profile. -/
def scenarioComplexity (scenario : CheckedScenario) : Complexity := {
  exprNodes := (complexity scenario.plan.parentProgram.body).exprNodes +
    (complexity scenario.plan.childProgram.body).exprNodes
  literalWeight := (complexity scenario.plan.parentProgram.body).literalWeight +
    (complexity scenario.plan.childProgram.body).literalWeight
}

/-- Transaction count, complete program size/literals, then runtime inputs,
call values and amounts. Every axis is a natural number and the comparison is
lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
    (scenarioComplexity candidate = scenarioComplexity source ∧
      valueWeight candidate < valueWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions, then per transaction: removal, bank replacements of the
input, the input with its child or root revert bit cleared, and smaller bank
call values and amounts. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for input in boundaryInputs do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with input := input})]
    for bit in [1, 2] do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
        {tx with input := tx.input.bitAnd (Word.ofNatModulo bit).bitNot})]
    for value in valueBank.filter (·.val < transaction.value.val) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with value := value})]
    for amount in valueBank.filter (·.val < transaction.amount.val) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with amount := amount})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("programs", programsJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", ForwardedCall.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from forwarded-value plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson emitted do throw "saved contract metadata differs from forwarded-value wrappers"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "forward-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated forwarded-value provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do
      throw "reduction parent programs differ from their plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentPrograms", programsJson parent.plan), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported forwarded-value case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentPrograms", programsJson source.plan), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson forwardCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.ForwardedCall
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.MethodsExecution
/-! Execute the original checked several-methods contract over a persistent
account world. A method has a name and a number of uint256 parameters; its
selector is the first four bytes of the Keccak-256 of its signature. A
transaction calls one method with its Word inputs in canonical calldata, or
sends a missing selector, matching no method, with one Word. `stdDispatch` is
a second model of the pinned std's dispatcher, written over the bytes instead
of in Core, which prescribes each transaction's outcome. Observations report
slots zero to five and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MethodsExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan Shape)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.methods-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Method where
  name : String
  arity : Nat
  deriving BEq, Repr

def Method.signature (method : Method) : String :=
  method.name ++ "(" ++ ",".intercalate (List.replicate method.arity "uint256") ++ ")"

/-- The first four bytes of a signature's Keccak-256, as std's `Selector`
computes them and the compiler checks them for collisions. -/
def selectorOf (signature : String) : Nat :=
  StdCalldata.bigEndian (Solcore.Abi.V1.Keccak256.hash signature.toUTF8) 0 4

def Method.selector (method : Method) : Nat := selectorOf method.signature

def Method.shape (method : Method) : Shape := ⟨method.selector, method.arity⟩

/-- A call of method `target` with its inputs, or, without a target, the
missing selector with one Word. -/
structure Transaction where
  id : String
  target : Option Nat
  inputs : List Word
  deriving BEq

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

/-- The selector a transaction sends. -/
def sentSelector (methods : List Method) (missing : Nat) (tx : Transaction) : Nat :=
  match tx.target with
  | some position => (methods.getD position ⟨"", 0⟩).selector
  | none => missing

/-- The canonical calldata: the selector, then each input Word. -/
def inputBytes (methods : List Method) (missing : Nat) (tx : Transaction) : ByteArray :=
  tx.inputs.foldl (fun bytes value => bytes ++ encodeWordBytesBE value)
    (selectorBytes (sentSelector methods missing tx))

/-- A call names a declared method and carries exactly its arguments; the
missing selector carries one Word. -/
def Transaction.valid (tx : Transaction) (methods : List Method) : Bool :=
  match tx.target with
  | some position => position < methods.length && tx.inputs.length == (methods.getD position ⟨"", 0⟩).arity
  | none => tx.inputs.length == 1

/-- The pinned std's dispatch over raw calldata: the position of the method that
runs, or the rejecting error selector. Calldata shorter than four bytes or with
no matching selector reaches the default fallback; the first method whose
selector matches, in declaration order, runs once its arguments' head exists. -/
def stdDispatch (shapes : List Shape) (input : ByteArray) : Except Nat Nat :=
  if input.size < 4 then .error noSelectorError
  else
    let selector := StdCalldata.bigEndian input 0 4
    match shapes.zipIdx.find? (fun (shape, _) => shape.selector == selector) with
    | none => .error noSelectorError
    | some (shape, position) =>
        if input.size < 4 + 32 * shape.arity then .error truncatedError else .ok position

def stdRejection? (shapes : List Shape) (input : ByteArray) : Option Nat :=
  match stdDispatch shapes input with
  | .error selector => some selector
  | .ok _ => none

def calldata (methods : List Method) (missing : Nat) (tx : Transaction) : String :=
  encodeBytesText (inputBytes methods missing tx)

def inputData? (methods : List Method) (missing : Nat) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes methods missing tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the shared accumulator, slot one the shared call count and
slots two to five the methods' accumulators. -/
def observedSlots : List Word :=
  (List.range Solcore.Synthesis.Core.ContractMethods.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the storage profiles, with
each transaction's calldata selecting its method. -/
def observeContract (contract : CheckedCoreContract) (methods : List Method) (missing : Nat)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? methods missing transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (methods : List Method) (missing : Nat) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract methods missing transactions bindings fuel

end Solcore.Synthesis.Stateful.MethodsExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.MethodsEmitter
/-! Emit the several-methods contract. Each method's step becomes the top-level
functions `sc_m{i}_fn{j}` and `sc_m{i}_step`, and each method a public function
of its name and `uint256` parameters, in declaration order, so the compiler
builds std's method tuple in the order the original Core contract dispatches.
A method's body follows the original Core protocol in order: the sum of its
arguments, the step, the writes of slots zero, one and `2 + i`, the reread sum
and the odd-input revert. Memory at zero is touched only before that revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Methods

open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan resultSlot)
open Solcore.Synthesis.Stateful.MethodsExecution (Method)

def emitterVersion : String := "solcore-source-methods-v1"
def wrapperVersion : String := "solcore-word-methods-contract-v1"
def contractName : String := "SynthesizedMethods"
def deployPath : List String := ["SynthesizedMethodsDeploy"]
def runtimePath : List String := ["SynthesizedMethodsDeploy", "SynthesizedMethods"]

/-- The emitted source of a several-methods contract; its methods are the case's. -/
structure EmittedMethods where
  source : String
  contractName : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

/-- Method `position`'s step: its helpers and its entry. -/
private def stepLines (position : Nat) (step : Aggregates.CheckedDAG) : Except EmitError (List String) := do
  let stem := "sc_m" ++ toString position
  let mut names : List String := []
  let mut lines : List String := []
  for (body, index) in step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := stem ++ "_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 step.entry
  let result ← AggregateRenderer.requireValue entry
  return lines ++ ["function " ++ stem ++ "_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", ""]

/-- Method `position`'s public function. -/
private def methodLines (position : Nat) (method : Method) : List String :=
  let arguments := (List.range method.arity).map fun index => "a" ++ toString index
  let input := if method.arity = 0 then "0" else
    " + ".intercalate (arguments.map fun argument => "Typedef.rep(" ++ argument ++ ")")
  let slot := toString (resultSlot position)
  ["    function " ++ method.name ++ "(" ++ ", ".intercalate (arguments.map (· ++ ": uint256")) ++
      ") public returns (uint256) {",
    "        let sc_input: word = " ++ input ++ ";",
    "        let sc_computed: word = sc_m" ++ toString position ++ "_step(sc_input + sload(0));",
    "        sstore(0, sc_computed);",
    "        sstore(1, sload(1) + 1);",
    "        sstore(" ++ slot ++ ", sc_computed);",
    "        let sc_result: word = sload(0) + sload(1) + sload(" ++ slot ++ ");",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);",
    "    }"]

def emit (plan : CheckedPlan) (methods : List Method) : Except EmitError EmittedMethods := do
  let bodies := plan.steps.flatMap fun step => step.helpers ++ [step.entry]
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"] bodies, ""]
  for (step, position) in plan.steps.zipIdx do
    lines := lines ++ (← stepLines position step)
  lines := lines ++ ["contract " ++ contractName ++ " {"]
  for (method, position) in methods.zipIdx do
    lines := lines ++ (if position = 0 then [] else [""]) ++ methodLines position method
  lines := lines ++ ["}"]
  return {source := String.intercalate "\n" lines ++ "\n", contractName, deployPath, runtimePath}

end Solcore.Synthesis.Source.Methods
end

section
-- leanmerge: from Solcore.Synthesis.Source.MethodsCases
/-! Several-methods cases retain one original host-aware Core contract with two
to four external methods, each with its own checked aggregate step over shared
slots, and an ordered history of calls. A transaction calls one recorded
method with recorded Word inputs, or sends the case's missing selector with one
Word. Each case records the methods' names, signatures, selectors, arities and
selector order. Reductions remove transactions, then methods no remaining
transaction calls, then simplify each step and the inputs. Saved outputs are
never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Methods
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan Shape minMethods maxMethods maxArity maxGuardNodes)
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction Bindings stdRejection? selectorOf)

def caseSchema : String := "solcore-lean.semantic-methods-case.v1"
def planSchema : String := "solcore-lean.methods-plan.v1"
def profileVersion : String := "stateful-methods-v1/methods-sequence-seed-v2"
def templateVersion : String := "std-dispatch-methods-shared-slots-revert-odd-input-v1"
def corpusSchema : String := "solcore-lean.semantic-methods-corpus.v1"

/-- Inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts may exceed the step budget by the methods' guards. -/
def maxProgramNodes : Nat := 512 + maxGuardNodes

private def hexDigits : List Char := "0123456789abcdef".toList

/-- `m_` and eight lowercase hexadecimal digits. -/
def validName (name : String) : Bool :=
  name.length == 10 && name.startsWith "m_" && (name.drop 2).all (hexDigits.contains ·)

def nameOf (value : Nat) : String :=
  "m_" ++ String.ofList ((List.range 8).reverse.map fun index => hexDigits.getD (value / 16 ^ index % 16) '0')

/-- The order of the method selectors, read in declaration order. -/
def selectorOrder (methods : List Method) : String :=
  let selectors := methods.map (·.selector)
  let pairs := selectors.zip (selectors.drop 1)
  if pairs.all (fun (left, right) => left < right) then "ascending"
  else if pairs.all (fun (left, right) => left > right) then "descending"
  else "mixed"

/-- Two to four methods with valid distinct names and at most two arguments;
the missing selector is a 32-bit value no method has, and no two selectors
coincide, as the compiler rejects colliding ones. -/
def validMethods (methods : List Method) (missing : Nat) : Bool :=
  let selectors := methods.map (·.selector)
  minMethods ≤ methods.length && methods.length ≤ maxMethods &&
    methods.all (fun method => validName method.name && method.arity ≤ maxArity) &&
    (methods.map (·.name)).Nodup && selectors.Nodup && missing < 2 ^ 32 && !selectors.contains missing

def validTransactions (methods : List Method) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧
    transactions.all (fun tx => Storage.validId tx.id && tx.valid methods) = true

instance (methods : List Method) (transactions : List Transaction) :
    Decidable (validTransactions methods transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  methods : List Method
  missing : Nat
  transactions : List Transaction
  shaped : (plan.shapes == methods.map (·.shape)) = true
  named : validMethods methods missing = true
  valid : validTransactions methods transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (methods : List Method) (missing : Nat) (transactions : List Transaction) :
    Except String CheckedScenario := do
  if shaped : (plan.shapes == methods.map (·.shape)) = true then
    if named : validMethods methods missing = true then
      if valid : validTransactions methods transactions then
        if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
          return ⟨plan, methods, missing, transactions, shaped, named, valid, bounded⟩
        else throw "canonical several-methods contract exceeds its case limit"
      else throw s!"several-methods scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each calling a declared method with its arguments or sending the missing selector with one Word"
    else throw "several-methods scenario requires two to four distinctly named methods of at most two arguments with distinct selectors and a missing selector none of them has"
  else throw "methods plan differs from the methods' selectors and arities"

def selectorText (selector : Nat) : String := Stateful.StdCalldata.selectorText selector

def prescribed (scenario : CheckedScenario) (tx : Transaction) : Option Nat :=
  stdRejection? scenario.plan.shapes
    (Solcore.Synthesis.Stateful.MethodsExecution.inputBytes scenario.methods scenario.missing tx)

def transactionJson (methods : List Method) (missing : Nat) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id),
  ("method", match tx.target with
    | some position => toJson (methods.getD position ⟨"", 0⟩).name
    | none => Json.null),
  ("selector", toJson (selectorText (Solcore.Synthesis.Stateful.MethodsExecution.sentSelector methods missing tx))),
  ("inputs", toJson (tx.inputs.map fun value => toString value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MethodsExecution.calldata methods missing tx)),
  ("stdRejection", match stdRejection? (methods.map (·.shape))
      (Solcore.Synthesis.Stateful.MethodsExecution.inputBytes methods missing tx) with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (methods : List Method) (missing : Nat) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson methods missing))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def selectorValue (text : String) : Except String Nat := do
  unless text.length == 10 && text.startsWith "0x" && (text.drop 2).all (hexDigits.contains ·) do
    throw "a selector is 0x and eight lowercase hexadecimal digits"
  return (text.drop 2).foldl (fun total digit => total * 16 + hexDigits.idxOf digit) 0

def decodeTransactions (methods : List Method) (missing : Nat) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let target ← match ← row.getObjVal? "method" with
      | .null => pure none
      | name => do
          let text ← name.getStr?
          let some position := methods.findIdx? (·.name == text) | throw "transaction names an undeclared method"
          pure (some position)
    let texts ← row.getObjValAs? (List String) "inputs"
    unless texts.length ≤ maxArity do throw "a transaction carries at most two inputs"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", target, ← texts.mapM word⟩
    unless Storage.validId transaction.id && transaction.valid methods do
      throw "invalid transaction ID or inputs for its method"
    unless row == transactionJson methods missing transaction do
      throw "transaction differs from canonical ID, method, selector, inputs, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions methods transactions do
    throw "several-methods scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) (methods : List Method) (missing : Nat) : Json := Json.mkObj [
  ("schema", toJson planSchema),
  ("methods", toJson ((methods.zip plan.steps).map fun (method, step) => Json.mkObj [
    ("name", toJson method.name), ("arity", toJson method.arity),
    ("stepProgram", Wire.encodeProgram step.program)])),
  ("missingSelector", toJson (selectorText missing))]

/-- The plan, its methods and the missing selector. -/
def checkedPlan (json : Json) : Except String (CheckedPlan × List Method × Nat) := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported several-methods plan schema"
  let rows ← json.getObjValAs? (List Json) "methods"
  unless minMethods ≤ rows.length && rows.length ≤ maxMethods do throw "a plan has two to four methods"
  let parts ← rows.mapM fun row => do
    let method : Method := ⟨← row.getObjValAs? String "name", ← row.getObjValAs? Nat "arity"⟩
    let step ← Aggregate.checkedFunction (← row.getObjVal? "stepProgram")
    pure (method, step)
  let methods := parts.map Prod.fst
  let missing ← selectorValue (← json.getObjValAs? String "missingSelector")
  unless validMethods methods missing do
    throw "plan methods need valid distinct names, at most two arguments and distinct selectors other than the missing one"
  let some plan := CheckedPlan.ofParts? (methods.map (·.shape)) (parts.map Prod.snd) |
    throw "several-methods contract failed full host-Core admission"
  unless json == planJson plan methods missing do throw "several-methods plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "several-methods contract exceeds its case limit"
  return (plan, methods, missing)

def emitted (plan : CheckedPlan) (methods : List Method) : Except String EmittedMethods :=
  (emit plan methods).mapError reprStr

def contractJson (methods : List Method) (emitted : EmittedMethods) : Json := Json.mkObj [
  ("name", toJson emitted.contractName),
  ("methods", toJson (methods.map fun method => Json.mkObj [
    ("name", toJson method.name), ("signature", toJson method.signature),
    ("selector", toJson (selectorText method.selector)), ("arity", toJson method.arity)])),
  ("selectorOrder", toJson (selectorOrder methods)),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedMethods) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("methodsPlan", planJson scenario.plan scenario.methods scenario.missing),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.methods scenario.missing scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MethodsExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ContractMethods.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson (scenario.plan.steps.flatMap (·.features)))]),
    ("contract", contractJson scenario.methods emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let source ← emitted scenario.plan scenario.methods
  return makeCase scenario source origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic several-methods case schema"
  let (plan, methods, missing) ← checkedPlan (← json.getObjVal? "methodsPlan")
  let transactions ← decodeTransactions methods missing (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical several-methods plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MethodsExecution.slotsJson do
    throw "observed slots must be zero through five"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan methods missing transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MethodsExecution.observe scenario.plan scenario.methods scenario.missing
    scenario.transactions bindings fuel

/-- The wrapping sum of a transaction's inputs; odd sums revert. -/
def inputSum (tx : Transaction) : Nat := tx.inputs.foldl (fun total value => (total + value.val) % 2 ^ 256) 0

def reverts (tx : Transaction) : Bool := inputSum tx % 2 == 1

/-- The method count, then each of four methods' name and arity, then the
missing method's name; each the high half of one draw from one stream of the
scenario seed. The stream starts at SplitMix64's finalizer of the seed xor its
domain, so that consecutive seeds' choices do not step by a fixed residue. -/
def shapeChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d6574686f64732d))
  let mut values : Array Nat := #[]
  for bound in [3] ++ (List.replicate maxMethods [2 ^ 32, 3]).flatten ++ [2 ^ 32] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The methods and the missing selector a scenario seed draws. -/
def drawnShape (seed : Seed) : List Method × Nat :=
  let choices := shapeChoices seed
  let count := minMethods + choices.getD 0 0
  let methods := (List.range count).map fun index =>
    (⟨nameOf (choices.getD (1 + 2 * index) 0), choices.getD (2 + 2 * index) 0⟩ : Method)
  let missing := (⟨nameOf (choices.getD (1 + 2 * maxMethods) 0), 1⟩ : Method).selector
  (methods, missing)

/-- Eight candidate step seeds for method `position`, each the finalizer of one
draw from the method's own stream; its step comes from the first that fits the
budget. The stream starts at the finalizer of the seed xor the domain
`"methstep" + position`, which no position below four carries out of its last
byte, so it meets neither the shape nor the sequence domain, and the
candidates' helper counts and templates are not affine in the seed. -/
def stepSeeds (seed : Seed) (position : Nat) : List Seed := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ (0x6d65746873746570 + position.toUInt64)))
  let mut values : Array Seed := #[]
  for _ in List.range 8 do
    let (value, next) := GeneratorV2.draw state
    values := values.push (Seed.ofUInt64 value)
    state := next
  return values.toList

/-- A target below `2n + 1` for `n` methods and two inputs for each of three
transactions, each the high half of one draw from a separate stream. The stream
starts at SplitMix64's finalizer of the seed xor its domain, so that consecutive
seeds' choices do not step by a fixed residue. -/
def sequenceChoices (count : Nat) (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d6574686f642d74))
  let mut values : Array Nat := #[]
  for bound in List.replicate 3 [2 * count + 1, 6, 6] |>.flatten do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Transaction `i` targets the missing selector when its target choice is
`2n`, otherwise method `choice % n`, so each method is called two times in
`2n + 1` and the missing selector once, with that method's arguments, or one
Word for the missing selector, from the boundary bank. -/
def blockTransactions (methods : List Method) (seed : Seed) (first : Nat) : List Transaction :=
  let count := methods.length
  let choices := sequenceChoices count seed
  (List.range 3).map fun index =>
    let choice := choices.getD (3 * index) 0
    let target := if choice < 2 * count then some (choice % count) else none
    let arity := match target with
      | some position => (methods.getD position ⟨"", 0⟩).arity
      | none => 1
    ⟨"tx-" ++ toString (first + index), target,
      (List.range arity).map fun argument => boundaryInputs.getD (choices.getD (3 * index + 1 + argument) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (methods : List Method) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions methods) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's input parity. -/
def completionName (scenario : CheckedScenario) (tx : Transaction) : String :=
  match prescribed scenario tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (reverts tx)

/-- The dispatch shell lies inside the node budget and the methods' guards
outside it; the methods share the rest equally. Each step comes from the first
of its method's candidate seeds whose template fits that share, under the
case's one swarm mask. The complete contract is remeasured as the final budget
authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.ContractMethods.programOverhead < nodes do
    throw "node budget is too small for the several-methods wrapper or exceeds 512"
  let (methods, missing) := drawnShape seed
  unless validMethods methods missing do throw "drawn method selectors collide"
  let budget := (nodes - Solcore.Synthesis.Core.ContractMethods.programOverhead) / methods.length
  let mask := revision.caseMask seed
  let mut steps : List Aggregates.CheckedDAG := []
  let mut stepOrigins : Array Json := #[]
  for position in List.range methods.length do
    let mut chosen : Option (Aggregates.CheckedDAG × Json) := none
    for (candidate, attempt) in (stepSeeds seed position).zipIdx do
      if chosen.isNone then
        if let .ok (step, stepOrigin) := Aggregate.generatedFunction candidate budget revision (some mask) then
          chosen := some (step, stepOrigin.setObjVal! "attempt" (toJson attempt))
    let some (step, stepOrigin) := chosen | throw "no candidate step seed fits the method's budget"
    steps := steps ++ [step]
    stepOrigins := stepOrigins.push stepOrigin
  let some plan := CheckedPlan.ofParts? (methods.map (·.shape)) steps |
    throw "generated several-methods plan failed full Core admission"
  let scenario ← checkedScenario plan methods missing (generatedTransactions methods seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + Solcore.Synthesis.Core.ContractMethods.guardNodes plan.shapes do
    throw "several-methods contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "methods-generated"), ("seed", toJson (toString seed.toNat)),
    ("maxProgramNodes", toJson nodes), ("shapeChoices", toJson (shapeChoices seed)),
    ("stepOrigins", .arr stepOrigins),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices (sequenceChoices methods.length) seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map (completionName scenario)))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; a call
completes with its input parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  for step in scenario.plan.steps do
    Aggregate.inputSensitive step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "several-methods history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "several-methods history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed scenario tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (reverts tx)) do
          throw "a several-methods call did not follow its input parity"
    prior := current

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let source ← emitted scenario.plan scenario.methods
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), source)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "several-methods history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "methods-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, source) =>
          cases := cases.push (makeCase scenario source origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => tx.inputs.foldl (fun sum value => sum + value.val) total) 0

/-- Transaction count, method count, complete program size/literals, then the
inputs. Every axis is a natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.methods.length < source.methods.length ∨
    (candidate.methods.length = source.methods.length ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        inputWeight candidate < inputWeight source)))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

/-- Each remaining method keeps its name and its step's helper count and
binding inventory. -/
def keepsSteps (candidate source : CheckedScenario) : Bool :=
  (candidate.methods.zip candidate.plan.steps).all fun (method, step) =>
    match source.methods.findIdx? (·.name == method.name) with
    | some position =>
        match source.plan.steps[position]? with
        | some original => step.helpers.length == original.helpers.length &&
            Aggregate.bindingInventory step == Aggregate.bindingInventory original
        | none => false
    | none => false

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameSteps : keepsSteps candidate source = true
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (methods : List Method) (steps : List Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? (methods.map (·.shape)) steps
  let candidate ← (checkedScenario plan methods source.missing transactions).toOption
  if same : keepsSteps candidate source = true then
    if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
      if strict : StrictlySmaller candidate source then some ⟨candidate, same, ids, strict⟩
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Without method `removed`, later positions move down by one. -/
private def retarget (removed : Nat) (tx : Transaction) : Transaction :=
  {tx with target := tx.target.map fun position => if position > removed then position - 1 else position}

/-- One-transaction removals first, from the last back; then the removal of
each method no transaction calls, from the last back; then each method's step
reductions; then each input replaced by zero or a smaller bank value.
Candidates still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let methods := source.methods
  let steps := source.plan.steps
  let mut raw : List (List Method × List Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(methods, steps,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for position in (List.range methods.length).reverse do
    if source.transactions.all (·.target != some position) then
      raw := raw ++ [(methods.eraseIdx position, steps.eraseIdx position, source.transactions.map (retarget position))]
  for (step, position) in steps.zipIdx do
    for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
      raw := raw ++ [(methods, steps.set position reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for (value, argument) in transaction.inputs.zipIdx do
      for smaller in boundaryInputs do
        if smaller.val < value.val then
          raw := raw ++ [(methods, steps, replaceAt source.transactions index fun tx =>
            {tx with inputs := tx.inputs.set argument smaller})]
  let mut seen : List String := []
  let mut result := []
  for (methods, steps, transactions) in raw do
    if let some reduced := sealReduction source methods steps transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.methods reduced.candidate.missing
          reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.ContractMethods.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let source ← emitted admitted.plan admitted.methods
  unless (← json.getObjValAs? String "source") = source.source do
    throw "saved source differs from the several-methods emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.methods source do
    throw "saved contract metadata differs from the several-methods wrapper"
  unless (← provenance.getObjVal? "features") == toJson (admitted.plan.steps.flatMap (·.features)) do
    throw "saved features differ from the checked steps"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "methods-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated several-methods provenance"
    unless planJson expected.plan expected.methods expected.missing == planJson admitted.plan admitted.methods admitted.missing &&
        transactionsJson expected.methods expected.missing expected.transactions ==
          transactionsJson admitted.methods admitted.missing admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let (parentPlan, parentMethods, parentMissing) ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentMethods parentMissing (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentMethods parentMissing parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless admitted.missing == parent.missing &&
        (sealReduction parent admitted.methods admitted.plan.steps admitted.transactions).isSome do
      throw "reduction does not keep the methods' steps and IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"),
        ("parentPlan", planJson parent.plan parent.methods parent.missing),
        ("parentProgram", Wire.encodeProgram parent.program),
        ("parentTransactions", transactionsJson parent.methods parent.missing parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported several-methods case origin"
  return makeCase admitted source origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"),
    ("parentPlan", planJson source.plan source.methods source.missing),
    ("parentProgram", Wire.encodeProgram source.program),
    ("parentTransactions", transactionsJson source.methods source.missing source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.Methods
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedCallCases
/-! A call case retains two original checked HostWire contracts and a role-based
transaction sequence. Every replay reconstructs both programs from the checked
step. Saved outcomes are never an oracle; the public nested executor selects
committed worlds and ordered logs. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedCall
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.NestedCallExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-call-case.v1"
def planSchema : String := "solcore-lean.call-plan.v1"
def profileVersion : String := "stateful-calls-v2/sequence-seed-v2"
def templateVersion : String := "two-account-word-call-v1"
def callCorpusSchema : String := "solcore-lean.semantic-call-corpus.v1"

def boundaryInputs : List Word :=
  (List.range 8).map Word.ofNatModulo ++ [Word.maximum, Word.ofNatModulo (2 ^ 255)]
abbrev validId := Storage.validId
abbrev validTransactions := Storage.validTransactions

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : NestedCall.combinedNodes plan.step ≤ 512

def programsJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("parent", Wire.encodeProgram plan.parentProgram), ("child", Wire.encodeProgram plan.childProgram)]

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : NestedCall.combinedNodes plan.step ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical call contracts exceeds the 512-node case limit"
  else throw s!"call scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("value", toJson "0"), ("target", toJson "parent"), ("callee", toJson "child")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let id ← row.getObjValAs? String "id"
    let inputText ← row.getObjValAs? String "input"
    unless inputText.length ≤ 78 do throw "transaction input exceeds a Word"
    let input ← Input.inputWord inputText
    let transaction : Transaction := ⟨id, input⟩
    unless row == transactionJson transaction do throw "transaction differs from canonical ID, input or role metadata"
    return transaction
  unless validTransactions transactions do throw "call scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported call plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "call contracts failed full host-Core admission"
  unless json == planJson plan do throw "call plan differs from its canonical checked representation"
  unless NestedCall.combinedNodes plan.step ≤ 512 do throw "call contracts exceeds the 512-node case limit"
  return plan

def contractsJson (emitted : EmittedContracts) : Json := Json.mkObj [
  ("parent", Json.mkObj [("name", toJson emitted.parentContractName), ("method", toJson "run"),
    ("signature", toJson emitted.parentMethodSignature), ("selector", toJson emitted.selector),
    ("deployPath", toJson emitted.parentDeployPath), ("runtimePath", toJson emitted.parentRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.parentConstructorValue)]),
  ("child", Json.mkObj [("name", toJson emitted.childContractName), ("entry", toJson "fallback"),
    ("payable", toJson true), ("inputBytes", toJson (32 : Nat)),
    ("deployPath", toJson emitted.childDeployPath), ("runtimePath", toJson emitted.childRuntimePath),
    ("constructorCalldata", toJson "0x"), ("constructorValue", toJson emitted.childConstructorValue)])]

def initialStateJson : Json := Json.mkObj [
  ("accounts", toJson [
    Json.mkObj [("role", toJson "parent"), ("balance", toJson "8"), ("storage", toJson ([] : List Json))],
    Json.mkObj [("role", toJson "child"), ("balance", toJson "0"), ("storage", toJson ([] : List Json))]]),
  ("callerBalance", toJson "0")]

abbrev observedSlotsJson := Storage.observedSlotsJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedContracts) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("callPlan", planJson scenario.plan),
    ("programs", programsJson scenario.plan), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson NestedCall.version), ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contracts", contractsJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic call case schema"
  let plan ← checkedPlan (← json.getObjVal? "callPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let originals ← json.getObjVal? "programs"
  for name in ["parent", "child"] do
    let program ← (Wire.decodeProgramWithBudget
      {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
      (← originals.getObjVal? name)).mapError (fun
        | .protocol error => error.toJson.compress
        | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
    let expected := if name == "parent" then plan.parentProgram else plan.childProgram
    unless Wire.encodeProgram program == Wire.encodeProgram expected do
      throw "saved original Core program differs from its canonical call plan"
  unless originals == programsJson plan do throw "saved program roles are not canonical"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial accounts differ from fixed balances and empty storage"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.NestedCallExecution.observe scenario.plan scenario.transactions bindings fuel

/-- Three boundary-input indices, each the high half of one draw from a separate
stream. The stream starts at SplitMix64's finalizer of the seed xor its domain,
so that consecutive seeds' indices do not step by a fixed residue, and the
indices do not share the step seed's helper-count and template digits. -/
def sequenceIndices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x63616c6c732d7371))
  let mut values : Array Nat := #[]
  for _ in List.range 3 do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % 10)
    state := next
  return values.toList

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  (sequenceIndices seed).zipIdx.map fun (inputIndex, index) =>
    ⟨"tx-" ++ toString (first + index), boundaryInputs[inputIndex]?.getD Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && NestedCall.programOverhead < nodes do
    throw "node budget is too small for the call wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - NestedCall.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated call plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless NestedCall.combinedNodes scenario.plan.step ≤ nodes do throw "call contracts exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "call-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceIndices", toJson (Stateful.Sequence.blocks (fun blockSeed _ => sequenceIndices blockSeed) seed
      transactions))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.NestedCallExecution.fixtureBindings fuel
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless (← observed.getObjValAs? String "status") = "complete" do
    if rows.any (fun row => (row.getObjValAs? String "status").toOption == some "out-of-fuel") then
      throw "call history exhausted Core fuel"
    else throw "call history stopped without a permitted root completion"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (if tx.input.val / 2 % 2 == 1 then "reverted" else "returned")) do
    throw "call history did not produce the prescribed root outcomes"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "call history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "call-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson callCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

def scenarioComplexity (scenario : CheckedScenario) : Complexity := {
  exprNodes := (complexity scenario.plan.parentProgram.body).exprNodes +
    (complexity scenario.plan.childProgram.body).exprNodes
  literalWeight := (complexity scenario.plan.parentProgram.body).literalWeight +
    (complexity scenario.plan.childProgram.body).literalWeight
}

/-- Transaction count, complete program size/literals, then runtime inputs.
Every axis is a natural number and the comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((scenarioComplexity candidate).StrictlySmaller (scenarioComplexity source) ∨
    (scenarioComplexity candidate = scenarioComplexity source ∧
      inputWeight candidate < inputWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let key := (Json.mkObj [("programs", programsJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", NestedCall.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from call plan emission"
  unless (← json.getObjVal? "contracts") == contractsJson emitted do throw "saved contract metadata differs from call wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "call-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated call provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentPrograms") == programsJson parent.plan do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentPrograms", programsJson parent.plan), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported call case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentPrograms", programsJson source.plan), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson callCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.NestedCall
end
