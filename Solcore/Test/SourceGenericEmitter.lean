import Solcore.Synthesis.Source.GenericEmitter
import Solcore.Core.Machine

/-! Monomorphic Core selection and a polymorphic source definition. Explicit
boundary goldens cover both selector branches, aggregate payloads and wrapping
addition. Private cell traces establish eager left-to-right candidate evaluation. -/
set_option autoImplicit false

namespace Tests.SourceGenericEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)
open Solcore.Synthesis.Source (EmittedProgram)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def incrementTwo : Wire.Expr := .binary .wordAdd (.var 0) (word 2)
private def arbitraryEntry : Wire.Expr := .binary .wordSub entry (word 1)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "generic step did not pass the aggregate checker")

private def checked (graph : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph variant with
  | some plan => pure plan
  | none => throw (IO.userError "generic monomorphic wrapper failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.Generic.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generic source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def identityExpected : Variant → List Nat
  | .word => [1, 1, Word.maximum.val, 2 ^ 255 + 1]
  | .pair => [2, 2, Word.maximum.val - 1, 2]
  | .sum => [2, 1, Word.maximum.val, 2 ^ 255 + 2]

private def incrementExpected : Variant → List Nat
  | .word => [2, 2, 0, 2 ^ 255 + 2]
  | .pair => [3, 3, Word.maximum.val, 3]
  | .sum => [3, 2, 0, 2 ^ 255 + 3]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied generic plan failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"generic result changed: {plan.variant.name}, input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "generic candidate evaluation was lazy, reordered or shared a private cell"
  | _ => throw (IO.userError "generic Core application did not return a Word")

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  let arbitrary ← step [incrementTwo] arbitraryEntry
  for variant in Variant.all do
    let identityPlan ← checked identity variant
    let arbitraryPlan ← checked arbitrary variant
    for (input, expected) in inputs.zip (identityExpected variant) do
      observe identityPlan input expected
        [Word.ofNatModulo input, Word.ofNatModulo (input + 1)]
    for (input, expected) in inputs.zip (incrementExpected variant) do
      observe arbitraryPlan input expected []
    match (identityPlan.instantiate Word.zero).toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was mistaken for generic completion")
  let constant ← checked (← step [word 42]) .word
  for input in inputs do observe constant input 42 []

private def admissionChecks : IO Unit := do
  for (variant, overhead) in Variant.all.zip [55, 79, 80] do
    ensure (Variant.ofString? variant.name == some variant) "generic variant is not canonical"
    for graph in [← step [identityWithCell], ← step [incrementTwo] arbitraryEntry] do
      let plan ← checked graph variant
      ensure (plan.program.check && plan.variant == variant &&
        plan.program.resultType == .function .word .word)
        "generic plan changed variant or escaped whole-program checking"
      match plan.program.body with
      | .letE saved (.letE (.lambda .bool _ _) (.lambda .word .word _)) =>
          ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
            "generic wrapper ignored its arbitrary checked step entry"
      | _ => throw (IO.userError "generic wrapper lost its explicit monomorphic selector closure")
      let measured := Wire.programNodes (plan.instantiate Word.maximum)
      ensure (measured == Generic.appliedNodes graph variant &&
        measured == Generic.canonicalNodes graph variant &&
        measured == Wire.programNodes graph.program + Generic.appliedOverhead variant &&
        Generic.appliedOverhead variant == overhead)
        "generic node overhead differs from the complete original Core application"
      ensure ((← emitted plan) == (← emitted plan)) "generic source emission is nondeterministic"
  for invalid in ["", "Word", "tuple", "sum<word,word>", "word "] do
    ensure (Variant.ofString? invalid).isNone "generic variant parsing accepted noncanonical metadata"
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  for variant in Variant.all do
    match Solcore.Synthesis.Source.Generic.emit (← checked divided variant) with
    | .ok emitted =>
        unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 &&
            (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
          throw (IO.userError "generic emission lost the raw division alias or its operand snapshots")
    | .error error => throw (IO.userError s!"generic raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [incrementTwo] arbitraryEntry
  let definition := String.intercalate "\n" [
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}"]
  let eager := String.intercalate "\n" [
    "        let sc_left_word: word = sc_step(sc_input);",
    "        let sc_next: word = sc_input + 1;",
    "        let sc_right_word: word = sc_step(sc_next);",
    "        let sc_flag: bool = ((sc_input & 1) == 1);"]
  for variant in Variant.all do
    let source ← emitted (← checked graph variant)
    ensure (contains source.source definition && contains source.source eager &&
      (source.source.splitOn "function sc_select<").length == 2 &&
      (source.source.splitOn " = sc_select(").length == 2)
      "generic source lost its polymorphic definition or eager ordered candidate calls"
    ensure (contains source.source (String.intercalate "\n" [
      "function sc_step(sc_arg: word) returns (word) {",
      "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 1;",
      "    let sc_v2: word = (sc_v0 - sc_v1);", "    return sc_v2;", "}"]))
      "generic source replaced the arbitrary entry with its last helper"
    ensure (source.contractName == "SynthesizedGenerics" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedGenericsDeploy"] &&
      source.runtimePath == ["SynthesizedGenericsDeploy", "SynthesizedGenerics"])
      "generic wrapper metadata changed"
    match variant with
    | .word =>
        ensure (contains source.source "let sc_selected: word = sc_select(")
          "Word generic instantiation disappeared"
    | .pair =>
        ensure (contains source.source "let sc_selected: (word, word) = sc_select(" &&
          contains source.source "sc_result = sc_first + sc_second;")
          "product generic instantiation lost its fields"
    | .sum =>
        ensure (contains source.source "let sc_selected: sum<word, word> = sc_select(" &&
          contains source.source "case inl(sc_payload)" && contains source.source "case inr(sc_payload)" &&
          contains source.source "sc_result = sc_payload + 1;")
          "sum generic instantiation lost its constructor-dependent result"
  ensure (Solcore.Synthesis.Source.Generic.emitterVersion == "solcore-source-generics-v2" &&
    Solcore.Synthesis.Source.Generic.wrapperVersion == "solcore-word-generics-contract-v1" &&
    Solcore.Synthesis.Source.Generic.selector == "0xa444f5e9" &&
    Generic.version == "core-generic-selection-plan-v1") "generic provenance changed"

def testSourceGenericEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceGenericEmitter
