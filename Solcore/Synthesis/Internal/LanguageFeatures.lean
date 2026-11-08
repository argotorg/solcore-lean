import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec

/-!
# Profiles: closures, comptime, generics, modules

The profiles `runtime-closures`, `runtime-comptime`, `runtime-generics` and `runtime-modules`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.ClosurePlan
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.ComptimePlan
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.GenericPlan
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.ModulePlan
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
end

section
-- leanmerge: from Solcore.Synthesis.Source.ClosureEmitter
/-! Source lambdas capture the current Word value of an outer local. Later
assignments exercise snapshot preservation, and a generic callable argument
forwards the second invocation. Only fixed local Word captures are admitted. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Closure

open Solcore.Synthesis.Core.Closure (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-closures-v2"
def wrapperVersion : String := "solcore-word-closures-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedClosures"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedClosuresDeploy"]
def runtimePath : List String := ["SynthesizedClosuresDeploy", "SynthesizedClosures"]

private def secondClosure : Variant → List String
  | .snapshot => [
      "        let sc_second: function (word) returns (word) = sc_first;"]
  | .independent => [
      "        let sc_second: function (word) returns (word) = lam (sc_arg: word) -> word {",
      "            return sc_cap + sc_arg;", "        };"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", ""]
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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_cap: word = sc_step(sc_input);",
    "        let sc_first: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "            return sc_cap + sc_arg;", "        };",
    "        sc_cap = sc_cap + 1;"] ++ secondClosure plan.variant ++ [
    "        sc_cap = sc_cap + 2;",
    "        let sc_a: word = sc_first(sc_input);",
    "        let sc_b: word = sc_apply(sc_second, sc_input + 1);",
    "        return uint256(3 * sc_a + sc_b + sc_cap);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Closure
end

section
-- leanmerge: from Solcore.Synthesis.Source.ClosureCases
/-! Closure cases retain a checked step DAG and capture variant. Every origin
reconstructs the actual original Core program, including explicit Word snapshots
before closure creation. Shrinking preserves the capture variant and step scope. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Closure
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Closure (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-closure-case.v1"
def planSchema : String := "solcore-lean.closure-plan.v1"
def profileVersion : String := "runtime-closures-v2/capture-seed-v1"
def templateVersion : String := "word-closure-snapshot-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("variant", toJson plan.variant.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported closure plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let variantText ← json.getObjValAs? String "variant"
  let some variant := Solcore.Synthesis.Core.Closure.Variant.ofString? variantText | throw "unsupported closure variant"
  let some plan := CheckedPlan.ofParts? step variant |
    throw "closure plan failed the full Core checker"
  unless json == planJson plan do throw "saved closure plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied closure exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("closurePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Closure.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied closure exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic closure case schema"
  let plan ← checkedPlan (← json.getObjVal? "closurePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical closure plan and runtime input"
  return ⟨plan, input⟩

def variantFor (seed : Seed) : Solcore.Synthesis.Core.Closure.Variant :=
  if seed.toNat / 3 % 2 = 0 then .snapshot else .independent

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let variant := variantFor seed
  let overhead := Solcore.Synthesis.Core.Closure.appliedOverhead variant
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected closure variant or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step variant |
    throw "generated closure plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied closure exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "closure-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("variant", toJson variant.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "closure boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "closure boundary observation produced a Core fault"

/-- Require both the generated step and the complete closure reference to
vary over the fixed boundary inputs. Imported and reduced constants remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all closure boundary inputs returned the same result"
  acceptance.check boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel acceptance
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "closure-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameVariant : candidate.plan.variant = source.plan.variant
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step source.plan.variant
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if variant : candidate.plan.variant = source.plan.variant then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, variant, strict⟩
        else none
      else none
    else none
  else none

/-- Step reductions retain all typed binders, including sum case payloads.
The closure variant is fixed; every candidate is fully checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × Word) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, input) in raw do
    if let some reduced := sealReduction source step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Closure.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical closure plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the closure wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "closure-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported closure case origin"
  if kind = "closure-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless planJson plan == planJson admitted.plan do
      throw "saved closure plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its closure boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    let acceptance ← Acceptance.ofOrigin origin
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "saved origin differs from generated closure provenance"
    inputSensitive plan validationFuel acceptance
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless admitted.plan.variant == parent.plan.variant &&
        (sealReduction parent admitted.plan.step admitted.input).isSome do
      throw "reduction changed its variant/binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask


def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Closure
end

section
-- leanmerge: from Solcore.Synthesis.Source.ComptimeEmitter
/-! Render the original closed G0 expression inside a genuine comptime-return
function. Its result passes a comptime parameter before materialization into the
runtime wrapper. The emitter never evaluates or substitutes that expression. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Comptime

open Solcore.Synthesis.Core.Comptime (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-comptime-v2"
def wrapperVersion : String := "solcore-word-comptime-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support

/-- The G0 features `emit` renders in the constant, those of `ScalarRenderer`. -/
def constantSupport := scalarSupport
def contractName : String := "SynthesizedComptime"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedComptimeDeploy"]
def runtimePath : List String := ["SynthesizedComptimeDeploy", "SynthesizedComptime"]

private def runtimeLines : Variant → List String
  | .offset => [
      "        let sc_result: word = sc_step(sc_input + sc_constant_value) + sc_constant_value;"]
  | .scale => [
      "        let sc_scale: word = sc_constant_value | 1;",
      "        let sc_result: word = sc_step(sc_input) * sc_scale + sc_constant_value;"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let constant ← ScalarRenderer.render .word [] 4 0 plan.constant.program.body
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_static(comptime value: word) returns (comptime<word>) {",
    "    return value;", "}", "",
    "function sc_constant() returns (comptime<word>) {"] ++ constant.lines ++
    ["    return sc_static(" ++ constant.value ++ ");", "}", ""]
  let mut names : List String := []
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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_constant_value: comptime<word> = sc_constant();"] ++ runtimeLines plan.variant ++
    ["        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Comptime
end

section
-- leanmerge: from Solcore.Synthesis.Source.ComptimeCases
/-! Comptime cases retain both original typed constant and runtime step ASTs.
Every origin reconstructs the complete executable Core reference, independent
of source staging. Constant, step and runtime input can shrink independently. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Comptime
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Comptime (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-comptime-case.v1"
def planSchema : String := "solcore-lean.comptime-plan.v1"
def profileVersion : String := "runtime-comptime-v2/constant-step-seed-v1"
def templateVersion : String := "original-word-comptime-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constantProgram", Wire.encodeProgram plan.constant.program),
  ("stepProgram", Wire.encodeProgram plan.step.program),
  ("variant", toJson plan.variant.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported comptime plan schema"
  let constant ← Solcore.Synthesis.Source.checkedProgram (← json.getObjVal? "constantProgram")
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let variantText ← json.getObjValAs? String "variant"
  let some variant := Solcore.Synthesis.Core.Comptime.Variant.ofString? variantText | throw "unsupported comptime variant"
  let some plan := CheckedPlan.ofParts? constant step variant |
    throw "comptime plan failed the full Core checker"
  unless json == planJson plan do throw "saved comptime plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied comptime exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("comptimePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Comptime.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features),
    ("constantFeatures", toJson ((features plan.constant.program.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied comptime exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic comptime case schema"
  let plan ← checkedPlan (← json.getObjVal? "comptimePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical comptime plan and runtime input"
  return ⟨plan, input⟩

def variantFor (seed : Seed) : Solcore.Synthesis.Core.Comptime.Variant :=
  if seed.toNat / 3 % 2 = 0 then .offset else .scale

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let variant := variantFor seed
  let overhead := Solcore.Synthesis.Core.Comptime.appliedOverhead variant
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected comptime variant or exceeds 512"
  let available := nodes - overhead
  let constantBudget := min 8 (available / 8)
  let constantSeed := Seed.ofNat (seed.toNat + 104729)
  -- The constant shares the case mask, restricted under revision four to the
  -- scalar renderer's features; that is the recorded step mask restricted alike.
  let mask := revision.caseMask seed constantSupport
  let generated ←
    (generate {seed := constantSeed, maxProgramNodes := constantBudget, revision, mask}).mapError reprStr
  let constant := generated.checkedProgram
  let constantOrigin := Json.mkObj [
    ("kind", toJson "generated"), ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes)]
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (available - constantBudget) revision
  let some plan := CheckedPlan.ofParts? constant step variant |
    throw "generated comptime plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied comptime exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "comptime-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("variant", toJson variant.name), ("constantOrigin", constantOrigin), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "comptime boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "comptime boundary observation produced a Core fault"

/-- This is an AST admission condition, not a claim that every operation is
reached. The actual complete Core execution supplies all boundary observations. -/
def constantUsesOperation (constant : CheckedWordProgram) : Bool :=
  (features constant.program.body).any fun
    | .unary _ | .binary _ | .ternary _ => true
    | _ => false

/-- Generation retains a nonliteral constant computation and an input-sensitive
runtime step. Imported and reduced literals and constant steps remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  unless constantUsesOperation plan.constant do throw "constant AST contains no operation"
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all comptime boundary inputs returned the same result"
  acceptance.check boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel acceptance
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "comptime-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameVariant : candidate.plan.variant = source.plan.variant
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (constant : CheckedWordProgram)
    (step : Aggregates.CheckedDAG) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? constant step source.plan.variant
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if variant : candidate.plan.variant = source.plan.variant then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, variant, strict⟩
        else none
      else none
    else none
  else none

/-- Constant reductions recheck closed G0 typing; step reductions retain all
typed binders, including sum case payloads.
The comptime variant is fixed; every candidate is fully checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (CheckedWordProgram × Aggregates.CheckedDAG × Word) := []
  for reduced in shrink source.plan.constant do
    raw := raw ++ [(reduced.checkedProgram, source.plan.step, source.input)]
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(source.plan.constant, reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.constant, source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (constant, step, input) in raw do
    if let some reduced := sealReduction source constant step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Comptime.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical comptime plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the comptime wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  unless (← provenance.getObjVal? "constantFeatures") ==
      toJson ((features admitted.plan.constant.program.body).map featureName) do
    throw "saved constant features differ from the original G0 expression"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "comptime-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported comptime case origin"
  if kind = "comptime-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless planJson plan == planJson admitted.plan do
      throw "saved comptime plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its comptime boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    let acceptance ← Acceptance.ofOrigin origin
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "saved origin differs from generated comptime provenance"
    inputSensitive plan validationFuel acceptance
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless admitted.plan.variant == parent.plan.variant &&
        (sealReduction parent admitted.plan.constant admitted.plan.step admitted.input).isSome do
      throw "reduction changed its variant/binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask


def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Comptime
end

section
-- leanmerge: from Solcore.Synthesis.Source.GenericEmitter
/-! Emit a genuinely polymorphic source selector, instantiated by the typed
arguments at Word, product or sum. The Core reference is independently built
with a monomorphic closure. `ScalarMeaning.Generic.emit_source_meaning`
relates the emitted text to the original Core result under an independent
generic source semantics; see `docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Generic

open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)

def emitterVersion : String := "solcore-source-generics-v2"
def wrapperVersion : String := "solcore-word-generics-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support
def contractName : String := "SynthesizedGenerics"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedGenericsDeploy"]
def runtimePath : List String := ["SynthesizedGenericsDeploy", "SynthesizedGenerics"]

private def selectedResult : Variant → List String
  | .word => [
      "        let sc_selected: word = sc_select(sc_flag, sc_left_word, sc_right_word);",
      "        return uint256(sc_selected);"]
  | .pair => [
      "        let sc_left: (word, word) = (sc_left_word, sc_input);",
      "        let sc_right: (word, word) = (sc_right_word, sc_next);",
      "        let sc_selected: (word, word) = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case (sc_first, sc_second) {",
      "                sc_result = sc_first + sc_second;",
      "            }", "        }",
      "        return uint256(sc_result);"]
  | .sum => [
      "        let sc_left: sum<word, word> = inl(sc_left_word);",
      "        let sc_right: sum<word, word> = inr(sc_right_word);",
      "        let sc_selected: sum<word, word> = sc_select(sc_flag, sc_left, sc_right);",
      "        let sc_result: word = 0;",
      "        match (sc_selected) {",
      "            case inl(sc_payload) {", "                sc_result = sc_payload;", "            }",
      "            case inr(sc_payload) {", "                sc_result = sc_payload + 1;", "            }",
      "        }", "        return uint256(sc_result);"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["",
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}", ""]
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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_left_word: word = sc_step(sc_input);",
    "        let sc_next: word = sc_input + 1;",
    "        let sc_right_word: word = sc_step(sc_next);",
    "        let sc_flag: bool = ((sc_input & 1) == 1);"] ++ selectedResult plan.variant ++
    ["    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Generic
end

section
-- leanmerge: from Solcore.Synthesis.Source.GenericCases
/-! Generic selection cases retain the checked step DAG and type variant.
The original Core reference is reconstructed for every origin; source uses a
polymorphic selection function while Core executes its checked specialization. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Generic
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Generic (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-generic-case.v1"
def planSchema : String := "solcore-lean.generic-plan.v1"
def profileVersion : String := "runtime-generics-v2/select-seed-v1"
def templateVersion : String := "eager-generic-select-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("variant", toJson plan.variant.name)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported generic plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let variantText ← json.getObjValAs? String "variant"
  let some variant := Solcore.Synthesis.Core.Generic.Variant.ofString? variantText | throw "unsupported generic variant"
  let some plan := CheckedPlan.ofParts? step variant |
    throw "generic plan failed the full Core checker"
  unless json == planJson plan do throw "saved generic plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied generic exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedProgram) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("genericPlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Generic.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features)]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied generic exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic generic case schema"
  let plan ← checkedPlan (← json.getObjVal? "genericPlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical generic plan and runtime input"
  return ⟨plan, input⟩

def variantFor (seed : Seed) : Solcore.Synthesis.Core.Generic.Variant :=
  match seed.toNat / 3 % 3 with
  | 0 => .word
  | 1 => .pair
  | _ => .sum

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let variant := variantFor seed
  let overhead := Solcore.Synthesis.Core.Generic.appliedOverhead variant
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the selected generic variant or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step variant |
    throw "generated generic plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied generic exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "generic-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("variant", toJson variant.name), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "generic boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "generic boundary observation produced a Core fault"

/-- Require both the generated step and the complete specialized reference to
vary over the fixed boundary inputs. Imported and reduced constants remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all generic boundary inputs returned the same result"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary) :
    Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "generic-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (inputSelection.record origin) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  sameVariant : candidate.plan.variant = source.plan.variant
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (step : Aggregates.CheckedDAG)
    (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step source.plan.variant
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if variant : candidate.plan.variant = source.plan.variant then
        if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
          some ⟨candidate, count, bindings, variant, strict⟩
        else none
      else none
    else none
  else none

/-- Step reductions retain all typed binders, including sum case payloads.
The generic variant is fixed; every candidate is fully checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × Word) := []
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (step, input) in raw do
    if let some reduced := sealReduction source step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Generic.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical generic plan"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the generic wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "generic-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported generic case origin"
  if kind = "generic-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless planJson plan == planJson admitted.plan do
      throw "saved generic plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its generic boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    unless origin == inputSelection.record canonicalOrigin do throw "saved origin differs from generated generic provenance"
    inputSensitive plan validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless admitted.plan.variant == parent.plan.variant &&
        (sealReduction parent admitted.plan.step admitted.input).isSome do
      throw "reduction changed its variant/binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask


def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Generic
end

section
-- leanmerge: from Solcore.Synthesis.Source.ModuleEmitter
/-! Four source modules exercise imported generics, closure captures and
compile-time computation together. Every provider contributes to the public
result. The bundle retains the complete original constant and step sources;
the entry alias is only a compatibility view of case.sol. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Modules

open Solcore.Synthesis.Core.Modules (CheckedPlan)

def emitterVersion : String := "solcore-source-modules-v2"
def wrapperVersion : String := "solcore-word-modules-contract-v1"

/-- The G0 features `emit` renders in the step: every operator and form. -/
def featureSupport := AggregateRenderer.support

/-- The G0 features `emit` renders in the constant, those of `ScalarRenderer`. -/
def constantSupport := scalarSupport
def sourceBundleSchema : String := "solcore-lean.source-bundle.v1"
def contractName : String := "SynthesizedModules"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedModulesDeploy"]
def runtimePath : List String := ["SynthesizedModulesDeploy", "SynthesizedModules"]

structure SourceFile where
  path : String
  source : String
  deriving Repr, BEq

structure EmittedBundle where
  source : String
  entry : String
  files : List SourceFile
  contractName : String
  methodName : String
  methodSignature : String
  selector : String
  deployPath : List String
  runtimePath : List String
  deriving Repr, BEq

/-- Canonical transport representation. Replay compares all file contents,
not just the entry alias used by older single-file clients. -/
def bundleJson (bundle : EmittedBundle) : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", .str sourceBundleSchema),
    ("entry", .str bundle.entry),
    ("files", .arr (bundle.files.map fun file => Lean.Json.mkObj [
      ("path", .str file.path), ("source", .str file.source)]).toArray)]

private def join (lines : List String) : String := String.intercalate "\n" lines ++ "\n"

private def commonSource (plan : CheckedPlan) : Except EmitError String := do
  let constant ← ScalarRenderer.render .word [] 4 0 plan.constant.program.body
  return join (["import * from std;",
    "export { sc_static, sc_constant, sc_apply, sc_select };", "",
    "function sc_static(comptime value: word) returns (comptime<word>) {",
    "    return value;", "}", "",
    "function sc_constant() returns (comptime<word>) {"] ++ constant.lines ++
    ["    return sc_static(" ++ constant.value ++ ");", "}", "",
    "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {",
    "    return f(x);", "}", "",
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}"])

private def leftSource (plan : CheckedPlan) : Except EmitError String := do
  let mut lines := ["import * from std;", "import { sc_apply } from common;"] ++
    AggregateRenderer.opcodeImports (plan.step.helpers ++ [plan.step.entry]) ++ ["export { sc_left };", ""]
  let mut names : List String := []
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  return join (lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "function sc_left(input: word, k: word) returns (word) {",
    "    let sc_cap: word = sc_step(input + k);",
    "    let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "        return sc_cap + sc_arg;", "    };",
    "    sc_cap = sc_cap + 1;",
    "    return sc_apply(sc_f, input) + sc_cap;", "}"])

private def rightSource : String := join [
  "import * from std;", "import { sc_apply } from common;", "export { sc_right };", "",
  "function sc_right(input: word, k: word) returns (word) {",
  "    let sc_cap: word = input ^ k;",
  "    let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
  "        return sc_cap + sc_arg;", "    };",
  "    sc_cap = sc_cap + 2;",
  "    return sc_apply(sc_f, input + 1) + sc_cap;", "}"]

private def entrySource : String := join [
  "import * from std;", "import * from std.dispatch;",
  "import { sc_constant, sc_select } from common;",
  "import { sc_left } from left;", "import { sc_right } from right;", "",
  "contract " ++ contractName ++ " {",
  "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_k: comptime<word> = sc_constant();",
  "        let sc_left_value: word = sc_left(sc_input, sc_k);",
  "        let sc_right_value: word = sc_right(sc_input, sc_k);",
  "        let sc_selected: word = sc_select((sc_input & 1) == 1, sc_left_value, sc_right_value);",
  "        return uint256(sc_selected + sc_left_value + 3 * sc_right_value + sc_k);",
  "    }", "}"]

def emit (plan : CheckedPlan) : Except EmitError EmittedBundle := do
  let common ← commonSource plan
  let left ← leftSource plan
  return {
    source := entrySource
    entry := "case.sol"
    files := [
      ⟨"case.sol", entrySource⟩, ⟨"common.sol", common⟩,
      ⟨"left.sol", left⟩, ⟨"right.sol", rightSource⟩]
    contractName, methodName, methodSignature, selector, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Modules
end

section
-- leanmerge: from Solcore.Synthesis.Source.ModuleCases
/-! Module cases retain both original typed ASTs and the complete fixed source
bundle. All origins reconstruct the original Core reference and every source
file; reduction changes typed ASTs and inputs, never arbitrary bundle contents. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Modules
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Modules (CheckedPlan)

def caseSchema : String := "solcore-lean.semantic-module-case.v1"
def planSchema : String := "solcore-lean.module-plan.v1"
def profileVersion : String := "runtime-modules-v2/bundle-seed-v1"
def templateVersion : String := "original-four-module-mix-v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.maximum, Word.ofNatModulo (2 ^ 255)]

structure CheckedInput where
  plan : CheckedPlan
  input : Word

def CheckedInput.program (value : CheckedInput) : Wire.Program :=
  value.plan.instantiate value.input

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constantProgram", Wire.encodeProgram plan.constant.program),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do
    throw "unsupported module plan schema"
  let constant ← Solcore.Synthesis.Source.checkedProgram (← json.getObjVal? "constantProgram")
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? constant step |
    throw "module plan failed the full Core checker"
  unless json == planJson plan do throw "saved module plan differs from its canonical checked representation"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ 512 do
    throw "canonical applied module exceeds the 512-node case limit"
  return plan

def observe (plan : CheckedPlan) (input : Word) (fuel : Nat) : Json :=
  let fields := match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ => [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def contractJson (emitted : EmittedBundle) (input : Word) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson (Input.calldata input)), ("constructorCalldata", toJson "0x")]

def makeCase (plan : CheckedPlan) (input : Word) (emitted : EmittedBundle)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema), ("modulePlan", planJson plan),
  ("program", Wire.encodeProgram (plan.instantiate input)),
  ("input", toJson (toString input.val)), ("source", toJson emitted.source),
  ("sourceBundle", bundleJson emitted),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin), ("profileVersion", toJson profileVersion),
    ("functionVersion", toJson Solcore.Synthesis.Core.Modules.version), ("templateVersion", toJson templateVersion),
    ("stepProfileVersion", toJson Aggregate.profileVersion),
    ("stepFunctionVersion", toJson Aggregates.version),
    ("stepTemplateVersion", toJson Aggregate.templateVersion),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson plan.step.features),
    ("constantFeatures", toJson ((features plan.constant.program.body).map featureName))]),
  ("contract", contractJson emitted input), ("executionFuel", toJson fuel),
  ("directCore", observe plan input fuel)]

def emitCase (plan : CheckedPlan) (input : Word) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  unless Wire.programNodes (plan.instantiate input) ≤ 512 do
    throw "canonical applied module exceeds the 512-node case limit"
  let emitted ← (emit plan).mapError reprStr
  return makeCase plan input emitted origin fuel revision mask

/-- Even imported and reduced cases must retain the exact canonical reference;
there is no origin for which a saved arbitrary Core program is trusted. -/
def caseProgram (json : Json) : Except String CheckedInput := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic module case schema"
  let plan ← checkedPlan (← json.getObjVal? "modulePlan")
  let input ← Input.inputWord (← json.getObjValAs? String "input")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram (plan.instantiate input) do
    throw "saved Core program differs from its canonical module plan and runtime input"
  return ⟨plan, input⟩

/-- The actual wrapper syntax supplies the step budget. The complete applied
program is measured and checked again after the independent step generator. -/
def generatedPlan (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1) :
    Except String (CheckedPlan × Json) := do
  let overhead := Solcore.Synthesis.Core.Modules.appliedOverhead
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the module composition or exceeds 512"
  let available := nodes - overhead
  let constantBudget := min 8 (available / 8)
  let constantSeed := Seed.ofNat (seed.toNat + 104729)
  -- The constant shares the case mask, restricted under revision four to the
  -- scalar renderer's features; that is the recorded step mask restricted alike.
  let mask := revision.caseMask seed constantSupport
  let generated ←
    (generate {seed := constantSeed, maxProgramNodes := constantBudget, revision, mask}).mapError reprStr
  let constant := generated.checkedProgram
  let constantOrigin := Json.mkObj [
    ("kind", toJson "generated"), ("seed", toJson (toString generated.initialSeed.toNat)),
    ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson generated.maxProgramNodes)]
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (available - constantBudget) revision
  let some plan := CheckedPlan.ofParts? constant step |
    throw "generated module plan failed the full Core checker"
  unless Wire.programNodes (plan.instantiate Word.zero) ≤ nodes do
    throw "canonical applied module exceeds its requested node budget"
  let origin := Json.mkObj [
    ("kind", toJson "module-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("constantOrigin", constantOrigin), ("stepOrigin", stepOrigin)]
  return (plan, origin)

def boundaryResults (plan : CheckedPlan) (fuel : Nat) : Except String (List Word) :=
  boundaryInputs.mapM fun input =>
    match (plan.instantiate input).toCore.runStateful fuel with
    | .done (.word value) _ => .ok value
    | .done _ _ => .error "module boundary observation did not return a Word"
    | .outOfFuel _ => .error "boundary observation exhausted Core fuel"
    | .fault _ _ => .error "module boundary observation produced a Core fault"

/-- This is an AST admission condition, not a claim that every operation is
reached. The actual complete Core execution supplies all boundary observations. -/
def constantUsesOperation (constant : CheckedWordProgram) : Bool :=
  (features constant.program.body).any fun
    | .unary _ | .binary _ | .ternary _ => true
    | _ => false

/-- Generation retains a nonliteral constant computation and an input-sensitive
runtime step. Imported and reduced literals and constant steps remain valid. -/
def inputSensitive (plan : CheckedPlan) (fuel : Nat)
    (acceptance : Acceptance := .profile) : Except String Unit := do
  unless constantUsesOperation plan.constant do throw "constant AST contains no operation"
  Aggregate.inputSensitive plan.step fuel
  let results ← boundaryResults plan fuel
  unless results.any (fun result => some result != results.head?) do
    throw "all module boundary inputs returned the same result"
  acceptance.check boundaryInputs results

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (inputSelection : InputSelection := .boundary)
    (acceptance : Acceptance := .profile) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        let (plan, origin) ← generatedPlan seed nodes revision
        let emitted ← (emit plan).mapError reprStr
        inputSensitive plan fuel acceptance
        return (plan, origin, emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "module-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "boundary-out-of-fuel"
              else if error == Acceptance.identityReason then "boundary-identity" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (plan, origin, emitted) =>
          for (input, inputIndex) in (inputSelection.inputs boundaryInputs seed).zipIdx do
            if cases.size < count then
              let origin := (origin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
                "validationFuel" (toJson fuel)
              cases := cases.push
                (makeCase plan input emitted (acceptance.record (inputSelection.record origin)) fuel revision
                  (revision.caseMask seed featureSupport))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

structure Reduction (source : CheckedInput) where private mk ::
  candidate : CheckedInput
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body)

private def sealReduction (source : CheckedInput) (constant : CheckedWordProgram)
    (step : Aggregates.CheckedDAG) (input : Word) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? constant step
  let candidate : CheckedInput := ⟨plan, input⟩
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if strict : (complexity candidate.program.body).StrictlySmaller (complexity source.program.body) then
        some ⟨candidate, count, bindings, strict⟩
      else none
    else none
  else none

/-- Constant reductions recheck closed G0 typing; step reductions retain all
typed binders, including sum case payloads.
The fixed module composition remains intact; every candidate is checked and strictly
smaller as a complete applied reference, including its runtime input. -/
def reductions (source : CheckedInput) : List (Reduction source) := Id.run do
  let mut raw : List (CheckedWordProgram × Aggregates.CheckedDAG × Word) := []
  for reduced in shrink source.plan.constant do
    raw := raw ++ [(reduced.checkedProgram, source.plan.step, source.input)]
  for reduced in Aggregate.reductions ⟨source.plan.step, source.input⟩ do
    raw := raw ++ [(source.plan.constant, reduced.candidate.function, reduced.candidate.input)]
  for input in boundaryInputs do raw := raw ++ [(source.plan.constant, source.plan.step, input)]
  let mut seen : List String := []
  let mut result := []
  for (constant, step, input) in raw do
    if let some reduced := sealReduction source constant step input then
      let key := (Wire.encodeProgram reduced.candidate.program).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.Modules.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision featureSupport
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the canonical module plan"
  unless (← json.getObjVal? "sourceBundle") == bundleJson emitted do
    throw "saved module bundle differs from all canonical source files"
  unless (← json.getObjVal? "contract") == contractJson emitted admitted.input do
    throw "saved contract metadata differs from the module wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step DAG"
  unless (← provenance.getObjVal? "constantFeatures") ==
      toJson ((features admitted.plan.constant.program.body).map featureName) do
    throw "saved constant features differ from the original G0 expression"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "module-generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported module case origin"
  if kind = "module-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "saved seed exceeds limit"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) featureSupport do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    let (plan, expectedOrigin) ← generatedPlan (Seed.ofNat seed) nodes revision
    unless planJson plan == planJson admitted.plan do
      throw "saved module plan differs from its generation seed"
    let inputIndex ← origin.getObjValAs? Nat "inputIndex"
    let inputSelection ← InputSelection.ofOrigin origin
    unless (inputSelection.inputs boundaryInputs (Seed.ofNat seed))[inputIndex]? = some admitted.input do
      throw "saved input differs from its module boundary index"
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    let canonicalOrigin := (expectedOrigin.setObjVal! "inputIndex" (toJson inputIndex)).setObjVal!
      "validationFuel" (toJson validationFuel)
    let acceptance ← Acceptance.ofOrigin origin
    unless origin == acceptance.record (inputSelection.record canonicalOrigin) do throw "saved origin differs from generated module provenance"
    inputSensitive plan validationFuel acceptance
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentInput ← Input.inputWord (← origin.getObjValAs? String "parentInput")
    let parent : CheckedInput := ⟨parentPlan, parentInput⟩
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its canonical plan and input"
    unless (sealReduction parent admitted.plan.constant admitted.plan.step admitted.input).isSome do
      throw "reduction changed step binders or did not strictly decrease"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentInput", toJson (toString parent.input.val))] do
      throw "noncanonical reduced origin"
  return makeCase admitted.plan admitted.input emitted origin fuel revision mask


def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedPureRevision provenance
  let mask ← savedMask provenance revision featureSupport
  let mut cases : Array Json := #[]
  for reduced in (reductions source).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"), ("parentProgram", Wire.encodeProgram source.program),
      ("parentPlan", planJson source.plan), ("parentInput", toJson (toString source.input.val))]
    cases := cases.push
      (← emitCase reduced.candidate.plan reduced.candidate.input origin fuel revision mask)
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr cases)]

end Solcore.Synthesis.Source.Modules
end
