import Solcore.Synthesis.Source.ClosureEmitter
import Solcore.Core.Machine

/-! Closure snapshots remain independent of a later outer assignment. Weighted
results distinguish the first and second capture, while actual heap observations
check one step execution and a separate mutable capture cell. -/
set_option autoImplicit false

namespace Tests.SourceClosureEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Closure (CheckedPlan Variant)
open Solcore.Synthesis.Source (EmittedProgram)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (word 2))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
private def arbitraryEntry : Wire.Expr := .binary .wordSub entry (word 1)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "closure step did not pass the aggregate checker")

private def checked (graph : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph variant with
  | some plan => pure plan
  | none => throw (IO.userError "closure wrapper failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.Closure.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"closure source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def identityExpected : Variant → List Nat
  | .snapshot => [4, 13, Word.maximum.val - 4, 2 ^ 255 + 4]
  | .independent => [5, 14, Word.maximum.val - 3, 2 ^ 255 + 5]

private def incrementExpected : Variant → List Nat
  | .snapshot => [9, 18, 0, 2 ^ 255 + 9]
  | .independent => [10, 19, 1, 2 ^ 255 + 10]

private def constantExpected : Variant → List Nat
  | .snapshot => [214, 218, 210, 214]
  | .independent => [215, 219, 211, 215]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied closure plan failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"closure result changed: {plan.variant.name}, input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "closure wrapper repeated its step or aliased its mutable capture with a private step cell"
  | _ => throw (IO.userError "closure Core application did not return a Word")

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  let arbitrary ← step [privateStep] arbitraryEntry
  let skippedHelper ← step [privateStep] (.var 0)
  let constant ← step [word 42]
  for variant in Variant.all do
    let identityPlan ← checked identity variant
    let arbitraryPlan ← checked arbitrary variant
    let skippedPlan ← checked skippedHelper variant
    let constantPlan ← checked constant variant
    for (input, expected) in inputs.zip (identityExpected variant) do
      observe identityPlan input expected
        [Word.ofNatModulo input, Word.ofNatModulo (input + 3)]
      observe skippedPlan input expected [Word.ofNatModulo (input + 3)]
    for (input, expected) in inputs.zip (incrementExpected variant) do
      observe arbitraryPlan input expected [Word.ofNatModulo 2, Word.ofNatModulo (input + 4)]
    for (input, expected) in inputs.zip (constantExpected variant) do
      observe constantPlan input expected [Word.ofNatModulo 45]
    match (identityPlan.instantiate Word.zero).toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was mistaken for closure completion")

private def admissionChecks : IO Unit := do
  for (variant, overhead) in Variant.all.zip [70, 78] do
    ensure (Variant.ofString? variant.name == some variant) "closure variant is not canonical"
    for graph in [← step [identityWithCell], ← step [privateStep] arbitraryEntry] do
      let plan ← checked graph variant
      ensure (plan.program.check && plan.variant == variant &&
        plan.program.resultType == .function .word .word)
        "closure plan changed variant or escaped whole-program checking"
      match plan.program.body with
      | .letE saved (.letE (.lambda (.function .word .word) _ _) (.lambda .word .word _)) =>
          ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
            "closure wrapper ignored its arbitrary checked step entry"
      | _ => throw (IO.userError "closure wrapper lost its higher-order apply closure")
      let measured := Wire.programNodes (plan.instantiate Word.maximum)
      ensure (measured == Closure.appliedNodes graph variant &&
        measured == Closure.canonicalNodes graph variant &&
        measured == Wire.programNodes graph.program + Closure.appliedOverhead variant &&
        Closure.appliedOverhead variant == overhead)
        "closure node overhead differs from the complete original Core application"
      ensure ((← emitted plan) == (← emitted plan)) "closure source emission is nondeterministic"
  for invalid in ["", "Snapshot", "alias", "independent ", "word"] do
    ensure (Variant.ofString? invalid).isNone "closure variant parsing accepted noncanonical metadata"
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  for variant in Variant.all do
    match Solcore.Synthesis.Source.Closure.emit (← checked divided variant) with
    | .ok emitted =>
        unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 &&
            (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
          throw (IO.userError "closure emission lost the raw division alias or its operand snapshots")
    | .error error => throw (IO.userError s!"closure raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [privateStep] arbitraryEntry
  let capturePrefix := String.intercalate "\n" [
    "        let sc_cap: word = sc_step(sc_input);",
    "        let sc_first: function (word) returns (word) = lam (sc_arg: word) -> word {",
    "            return sc_cap + sc_arg;", "        };", "        sc_cap = sc_cap + 1;"]
  let calls := String.intercalate "\n" [
    "        sc_cap = sc_cap + 2;", "        let sc_a: word = sc_first(sc_input);",
    "        let sc_b: word = sc_apply(sc_second, sc_input + 1);",
    "        return uint256(3 * sc_a + sc_b + sc_cap);"]
  for variant in Variant.all do
    let source ← emitted (← checked graph variant)
    ensure (contains source.source capturePrefix && contains source.source calls &&
      contains source.source "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(x);\n}" &&
      (source.source.splitOn " = sc_step(sc_input);").length == 2 &&
      (source.source.splitOn " = sc_apply(").length == 2)
      "closure source changed snapshot timing, repeated the step or bypassed generic forwarding"
    ensure (contains source.source (String.intercalate "\n" [
      "function sc_step(sc_arg: word) returns (word) {",
      "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 1;",
      "    let sc_v2: word = (sc_v0 - sc_v1);", "    return sc_v2;", "}"]))
      "closure source replaced the arbitrary entry with its last helper"
    ensure (source.contractName == "SynthesizedClosures" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedClosuresDeploy"] &&
      source.runtimePath == ["SynthesizedClosuresDeploy", "SynthesizedClosures"])
      "closure wrapper metadata changed"
    match variant with
    | .snapshot =>
        ensure (contains source.source
          "sc_cap = sc_cap + 1;\n        let sc_second: function (word) returns (word) = sc_first;\n        sc_cap = sc_cap + 2;" &&
          (source.source.splitOn " = lam (").length == 2)
          "snapshot source recreated its first closure after mutation"
    | .independent =>
        ensure (contains source.source (String.intercalate "\n" [
          "        sc_cap = sc_cap + 1;",
          "        let sc_second: function (word) returns (word) = lam (sc_arg: word) -> word {",
          "            return sc_cap + sc_arg;", "        };", "        sc_cap = sc_cap + 2;"]) &&
          (source.source.splitOn " = lam (").length == 3)
          "independent source lost the second capture's distinct creation time"
  ensure (Solcore.Synthesis.Source.Closure.emitterVersion == "solcore-source-closures-v2" &&
    Solcore.Synthesis.Source.Closure.wrapperVersion == "solcore-word-closures-contract-v1" &&
    Solcore.Synthesis.Source.Closure.selector == "0xa444f5e9" &&
    Closure.version == "core-closure-capture-plan-v1") "closure provenance changed"

def testSourceClosureEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceClosureEmitter
