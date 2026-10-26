import Solcore.Synthesis.Source.ComptimeEmitter
import Solcore.Core.Machine

/-! The original constant AST executes in Core independently of Rust staging.
Golden results exercise branch-local bindings, all emitted scalar operations,
Word wrapping and an odd runtime scale. The heap contains only the single
runtime step's private effects. -/
set_option autoImplicit false

namespace Tests.SourceComptimeEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Comptime (CheckedPlan Variant)
open Solcore.Synthesis.Source (EmittedProgram)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (word 2))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))

/-- A closed branch with a live let-bound Word; its result is fifteen. -/
private def branchConstant : Wire.Expr :=
  .letE (word 7)
    (.ifE (.unary .boolNot (.binary .wordGt (.var 0) (word 7)))
      (.binary .wordXor (.binary .wordAdd (.var 0) (word 5)) (word 3)) (word 99))

/-- max+1=0, 0-1=max, max*2=max-1, then not/or/and/xor yield six.
Both conditional tests use the retained final Word, not a host-computed result. -/
private def wrappingConstant : Wire.Expr :=
  .letE (word Word.maximum.val)
    (.letE (.binary .wordAdd (.var 0) (word 1))
      (.letE (.binary .wordSub (.var 0) (word 1))
        (.letE (.binary .wordMul (.var 0) (word 2))
          (.letE (.unary .wordNot (.var 0))
            (.letE (.binary .wordOr (.var 0) (word 4))
              (.letE (.binary .wordAnd (.var 0) (word 7))
                (.letE (.binary .wordXor (.var 0) (word 3))
                  (.ifE (.unary .boolNot (.binary .wordGt (.var 0) (word 7)))
                    (.ifE (.binary .wordEq (.var 0) (word 6)) (.var 0) (word 99))
                    (word 123)))))))))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def constant (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some program => pure program
  | none => throw (IO.userError "comptime constant did not pass closed G0 admission")

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "comptime runtime step did not pass aggregate admission")

private def checked (closed : CheckedWordProgram) (graph : Aggregates.CheckedDAG)
    (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? closed graph variant with
  | some plan => pure plan
  | none => throw (IO.userError "comptime wrapper failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.Comptime.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"comptime source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied comptime plan failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"comptime result changed: {plan.variant.name}, input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "comptime wrapper repeated the runtime step or added effects to closed evaluation"
  | _ => throw (IO.userError "comptime Core application did not return a Word")

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  let constants := [
    (branchConstant, 15, [30, 31, 29, 2 ^ 255 + 30], [15, 30, 0, 2 ^ 255 + 15]),
    (wrappingConstant, 6, [12, 13, 11, 2 ^ 255 + 12], [6, 13, Word.maximum.val, 2 ^ 255 + 6]),
    (word 0, 0, inputs, inputs),
    (word Word.maximum.val, Word.maximum.val,
      [Word.maximum.val - 1, Word.maximum.val, Word.maximum.val - 2, 2 ^ 255 - 2],
      [Word.maximum.val, Word.maximum.val - 1, 0, 2 ^ 255 - 1]),
    (word (2 ^ 255), 2 ^ 255, inputs, [2 ^ 255, 1, Word.maximum.val, 0])]
  for (body, value, offsets, scales) in constants do
    let original ← constant body
    match original.program.toCore.runStateful 10000 with
    | .done (.word result) [] =>
        ensure (result.val == value) "closed original AST changed its independently known Word result"
    | _ => throw (IO.userError "closed G0 expression failed or allocated a cell")
    for variant in Variant.all do
      let plan ← checked original identity variant
      let results := if variant == .offset then offsets else scales
      for (input, expected) in inputs.zip results do
        let argument := if variant == .offset then input + value else input
        observe plan input expected [Word.ofNatModulo argument]
  let arbitrary ← step [privateStep] (.binary .wordSub entry (word 1))
  for (variant, results) in [
    (Variant.offset, [13, 14, 12, 2 ^ 255 + 13]),
    (Variant.scale, [13, 20, 6, 2 ^ 255 + 13])] do
    let plan ← checked (← constant wrappingConstant) arbitrary variant
    for (input, expected) in inputs.zip results do
      observe plan input expected [Word.ofNatModulo 2]
    match (plan.instantiate Word.zero).toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was mistaken for a completed staged computation")

private def admissionChecks : IO Unit := do
  let closed ← constant wrappingConstant
  for (variant, overhead) in Variant.all.zip [10, 12] do
    ensure (Variant.ofString? variant.name == some variant) "comptime variant is not canonical"
    for graph in [← step [identityWithCell], ← step [privateStep] (.binary .wordSub entry (word 1))] do
      let plan ← checked closed graph variant
      ensure (plan.program.check && plan.variant == variant &&
        plan.program.resultType == .function .word .word)
        "comptime plan changed variant or escaped whole-program checking"
      match plan.program.body with
      | .letE savedConstant (.letE savedStep (.lambda .word .word _)) =>
          ensure (Wire.encodeExpr savedConstant == Wire.encodeExpr closed.program.body &&
            Wire.encodeExpr savedStep == Wire.encodeExpr graph.program.body)
            "comptime wrapper substituted a computed value or changed its original entry"
      | _ => throw (IO.userError "comptime wrapper lost its single constant-before-step binding")
      let measured := Wire.programNodes (plan.instantiate Word.maximum)
      ensure (measured == Comptime.appliedNodes closed graph variant &&
        measured == Comptime.canonicalNodes closed graph variant &&
        measured == Wire.programNodes closed.program + Wire.programNodes graph.program + Comptime.appliedOverhead variant &&
        Comptime.appliedOverhead variant == overhead)
        "comptime node overhead omitted part of the original constant or runtime program"
      ensure ((← emitted plan) == (← emitted plan)) "comptime source emission is nondeterministic"
  for invalid in ["", "Offset", "multiply", "scale ", "word"] do
    ensure (Variant.ofString? invalid).isNone "comptime variant parsing accepted noncanonical metadata"
  for body in [.var 0, .loadCell (.newCell .word (word 7))] do
    ensure (CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body}).isNone
      "comptime plan admitted an open or effectful constant"
  -- Constants keep the scalar renderer; step functions render raw primitives.
  let unsupported ← constant (.ifE (.bool true) (word 0) (.binary .wordDiv (word 1) (word 1)))
  let dividedStep ← step [.binary .wordDiv (.var 0) (word 1)]
  for variant in Variant.all do
    match Solcore.Synthesis.Source.Comptime.emit (← checked unsupported (← step [identityWithCell]) variant) with
    | .error (.unsupportedBinary .wordDiv) => pure ()
    | _ => throw (IO.userError "comptime emission discarded an unsupported original constant")
    match Solcore.Synthesis.Source.Comptime.emit (← checked closed dividedStep variant) with
    | .ok emitted => unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
        throw (IO.userError "comptime step lost the raw division alias or its operand snapshots")
    | .error error => throw (IO.userError s!"comptime raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [privateStep] (.binary .wordSub entry (word 1))
  for variant in Variant.all do
    let source ← emitted (← checked (← constant wrappingConstant) graph variant)
    ensure (contains source.source
      "function sc_static(comptime value: word) returns (comptime<word>) {\n    return value;\n}" &&
      contains source.source "function sc_constant() returns (comptime<word>) {" &&
      contains source.source "let sc_constant_value: comptime<word> = sc_constant();" &&
      (source.source.splitOn "return sc_static(").length == 2 &&
      (source.source.splitOn "function sc_constant()").length == 2)
      "source lost its genuine comptime parameter/return boundary"
    for token in [" + ", " - ", " * ", " | ", " & ", " ^ ", "(~", "(!", " > ", " == ", "if ("] do
      ensure (contains source.source token) s!"source precomputed or dropped the original closed operation: {token}"
    ensure (contains source.source (String.intercalate "\n" [
      "function sc_step(sc_arg: word) returns (word) {",
      "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 1;",
      "    let sc_v2: word = (sc_v0 - sc_v1);", "    return sc_v2;", "}"]))
      "comptime source replaced the arbitrary runtime entry"
    ensure (source.contractName == "SynthesizedComptime" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedComptimeDeploy"] &&
      source.runtimePath == ["SynthesizedComptimeDeploy", "SynthesizedComptime"])
      "comptime wrapper metadata changed"
    match variant with
    | .offset =>
        ensure (contains source.source "sc_step(sc_input + sc_constant_value) + sc_constant_value;")
          "offset staging no longer affects the argument and result"
    | .scale =>
        ensure (contains source.source "let sc_scale: word = sc_constant_value | 1;" &&
          contains source.source "sc_step(sc_input) * sc_scale + sc_constant_value;")
          "scale staging lost its odd multiplier or result offset"
  ensure (Solcore.Synthesis.Source.Comptime.emitterVersion == "solcore-source-comptime-v2" &&
    Solcore.Synthesis.Source.Comptime.wrapperVersion == "solcore-word-comptime-contract-v1" &&
    Solcore.Synthesis.Source.Comptime.selector == "0xa444f5e9" &&
    Comptime.version == "core-comptime-word-plan-v1") "comptime provenance changed"

def testSourceComptimeEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceComptimeEmitter
