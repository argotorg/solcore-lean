import Solcore.Synthesis.Source.ModuleEmitter
import Solcore.Core.Machine

/-! The complete original Core program supplies the oracle independently of
Rust module loading and specialization. Fixed arithmetic results distinguish
both capture snapshots, provider order, selector branches and Word overflow.
Heap observations also expose repeated steps or aliased provider locals. -/
set_option autoImplicit false

namespace Tests.SourceModuleEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Modules (CheckedPlan)
open Solcore.Synthesis.Source.Modules (EmittedBundle)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (word 0))
    (.letE (.storeCell (.var 0) (word 2))
      (.binary .wordAdd (.var 2) (.loadCell (.var 1))))
private def arbitraryEntry : Wire.Expr :=
  .binary .wordSub (.first (.pair entry (.var 0))) (word 1)

private def branchConstant : Wire.Expr :=
  .letE (word 7)
    (.ifE (.unary .boolNot (.binary .wordGt (.var 0) (word 7)))
      (.binary .wordXor (.binary .wordAdd (.var 0) (word 5)) (word 3)) (word 99))

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
  | none => throw (IO.userError "module constant failed closed G0 admission")

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "module step failed aggregate admission")

private def checked (closed : CheckedWordProgram) (graph : Aggregates.CheckedDAG) : IO CheckedPlan :=
  match CheckedPlan.ofParts? closed graph with
  | some plan => pure plan
  | none => throw (IO.userError "module composition failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedBundle :=
  match Solcore.Synthesis.Source.Modules.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"module source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied module program failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"module composition changed: input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "module composition repeated its step, changed provider order or aliased capture cells"
  | _ => throw (IO.userError "module Core application did not return a Word")

private def rightCell (input k : Nat) : Word :=
  Word.ofNatModulo (((Word.ofNatModulo input).bitXor (Word.ofNatModulo k)).val + 2)

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  -- Independently calculated results; no Rust specialization supplies these constants.
  let constants := [
    (branchConstant, 15, [178, 179, Word.maximum.val - 18, 2 ^ 255 + 178]),
    (wrappingConstant, 6, [79, 92, Word.maximum.val - 9, 2 ^ 255 + 79]),
    (word 0, 0, [13, 26, Word.maximum.val - 3, 2 ^ 255 + 13]),
    (word Word.maximum.val, Word.maximum.val, [2, 3, Word.maximum.val - 2, 2 ^ 255 + 2]),
    (word (2 ^ 255), 2 ^ 255, [2 ^ 255 + 13, 2 ^ 255 + 26, 2 ^ 255 - 4, 13])]
  for (body, k, results) in constants do
    let closed ← constant body
    match closed.program.toCore.runStateful 10000 with
    | .done (.word value) [] => ensure (value.val == k) "original constant AST result changed"
    | _ => throw (IO.userError "closed module constant allocated a cell or failed")
    let plan ← checked closed identity
    for (input, expected) in inputs.zip results do
      observe plan input expected [Word.ofNatModulo (input + k),
        Word.ofNatModulo (input + k + 1), rightCell input k]
  let closed ← constant branchConstant
  let arbitrary ← checked closed (← step [privateStep] arbitraryEntry)
  for (input, expected) in inputs.zip [180, 183, Word.maximum.val - 14, 2 ^ 255 + 180] do
    observe arbitrary input expected
      [Word.ofNatModulo 2, Word.ofNatModulo (input + 17), rightCell input 15]
  let skipped ← checked closed (← step [privateStep] (.var 0))
  for (input, expected) in inputs.zip [178, 179, Word.maximum.val - 18, 2 ^ 255 + 178] do
    observe skipped input expected [Word.ofNatModulo (input + 16), rightCell input 15]
  let fixed ← checked closed (← step [word 42])
  for (input, expected) in inputs.zip [232, 283, 93, 2 ^ 255 + 232] do
    observe fixed input expected [Word.ofNatModulo 43, rightCell input 15]
  match (arbitrary.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was mistaken for module composition completion")

private def admissionChecks : IO Unit := do
  let closed ← constant wrappingConstant
  for graph in [← step [identityWithCell], ← step [privateStep] arbitraryEntry] do
    let plan ← checked closed graph
    ensure (plan.program.check && plan.program.resultType == .function .word .word)
      "module plan escaped whole-program checking"
    match plan.program.body with
    | .letE savedConstant (.letE savedStep (.letE (.lambda (.function .word .word) _ _)
        (.letE (.lambda .bool _ _) (.letE (.lambda .word _ _)
          (.letE (.lambda .word _ _) (.lambda .word .word _)))))) =>
        ensure (Wire.encodeExpr savedConstant == Wire.encodeExpr closed.program.body &&
          Wire.encodeExpr savedStep == Wire.encodeExpr graph.program.body)
          "module reference precomputed a constant or replaced its arbitrary step entry"
    | _ => throw (IO.userError "module reference lost a real apply/select/provider closure")
    let measured := Wire.programNodes (plan.instantiate Word.maximum)
    ensure (measured == Modules.appliedNodes closed graph &&
      measured == Modules.canonicalNodes closed graph &&
      measured == Wire.programNodes closed.program + Wire.programNodes graph.program + Modules.appliedOverhead &&
      Modules.appliedOverhead == 160)
      "module node budget omitted an original program or part of the composition"
    ensure ((← emitted plan) == (← emitted plan)) "module emission is nondeterministic"
  for body in [.var 0, .loadCell (.newCell .word (word 7))] do
    ensure (CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body}).isNone
      "module plan admitted an open or effectful constant"
  -- Constants keep the scalar renderer; step functions render raw primitives.
  let unsupported ← constant (.ifE (.bool true) (word 0) (.binary .wordDiv (word 1) (word 1)))
  let dividedStep ← step [.binary .wordDiv (.var 0) (word 1)] (.var 0)
  match Solcore.Synthesis.Source.Modules.emit (← checked unsupported (← step [identityWithCell])) with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "module emission silently omitted an unsupported original constant")
  match Solcore.Synthesis.Source.Modules.emit (← checked closed dividedStep) with
  | .ok bundle =>
      let some left := bundle.files.find? (·.path == "left.sol") | throw (IO.userError "module bundle lost left.sol")
      unless (left.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 &&
          (left.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 &&
          bundle.files.all (fun file => file.path == "left.sol" || (file.source.splitOn "sc_div").length == 1) do
        throw (IO.userError "module step lost the raw division alias, its snapshots or its file")
  | .error error => throw (IO.userError s!"module raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def fileSource (bundle : EmittedBundle) (path : String) : IO String :=
  match bundle.files.find? (fun file => file.path == path) with
  | some file => pure file.source
  | none => throw (IO.userError s!"module bundle is missing {path}")

private def formattingChecks : IO Unit := do
  let graph ← step [privateStep] arbitraryEntry
  let bundle ← emitted (← checked (← constant wrappingConstant) graph)
  ensure (bundle.entry == "case.sol" &&
    bundle.files.map (·.path) == ["case.sol", "common.sol", "left.sol", "right.sol"] &&
    bundle.source == (← fileSource bundle "case.sol"))
    "module bundle paths, ordering or entry alias changed"
  ensure (Solcore.Synthesis.Source.Modules.bundleJson bundle == Lean.Json.mkObj [
    ("schema", .str "solcore-lean.source-bundle.v1"), ("entry", .str "case.sol"),
    ("files", .arr (bundle.files.map fun file => Lean.Json.mkObj [
      ("path", .str file.path), ("source", .str file.source)]).toArray)])
    "module transport omitted a provider or changed canonical fields"
  let common ← fileSource bundle "common.sol"
  let left ← fileSource bundle "left.sol"
  let right ← fileSource bundle "right.sol"
  for file in bundle.files do
    ensure (file.source.startsWith "import * from std;\n" && file.source.endsWith "\n")
      "module lost its local standard-library evidence or terminal newline"
  for token in [" + ", " - ", " * ", " | ", " & ", " ^ ", "(~", "(!", " > ", " == ", "if ("] do
    ensure (contains common token) s!"common module dropped original constant operation {token}"
  ensure (contains common "export { sc_static, sc_constant, sc_apply, sc_select };" &&
    contains common "function sc_static(comptime value: word) returns (comptime<word>) {" &&
    contains common "function sc_constant() returns (comptime<word>) {" &&
    contains common "return sc_static(" &&
    contains common "function sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {" &&
    contains common "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {")
    "common module lost its real comptime or polymorphic definitions"
  for (provider, name, initial, increment, argument) in [
    (left, "left", "sc_step(input + k)", "1", "input"),
    (right, "right", "input ^ k", "2", "input + 1")] do
    ensure (contains provider "import { sc_apply } from common;" &&
      contains provider ("export { sc_" ++ name ++ " };") &&
      contains provider (String.intercalate "\n" [
        "    let sc_cap: word = " ++ initial ++ ";",
        "    let sc_f: function (word) returns (word) = lam (sc_arg: word) -> word {",
        "        return sc_cap + sc_arg;", "    };",
        "    sc_cap = sc_cap + " ++ increment ++ ";",
        "    return sc_apply(sc_f, " ++ argument ++ ") + sc_cap;"]))
      "provider changed capture timing or bypassed its imported generic call"
  ensure (contains left "function sc_step(sc_arg: word) returns (word) {" &&
    contains left "sc_fn0(sc_arg)" && contains left "match (" && contains left " - ")
    "left module replaced the arbitrary aggregate step with its last helper"
  ensure (contains bundle.source (String.intercalate "\n" [
    "import { sc_constant, sc_select } from common;",
    "import { sc_left } from left;", "import { sc_right } from right;"]) &&
    contains bundle.source (String.intercalate "\n" [
      "        let sc_k: comptime<word> = sc_constant();",
      "        let sc_left_value: word = sc_left(sc_input, sc_k);",
      "        let sc_right_value: word = sc_right(sc_input, sc_k);",
      "        let sc_selected: word = sc_select((sc_input & 1) == 1, sc_left_value, sc_right_value);",
      "        return uint256(sc_selected + sc_left_value + 3 * sc_right_value + sc_k);"]))
    "entry changed provider order or dropped a provider from its result"
  ensure (bundle.contractName == "SynthesizedModules" && bundle.methodName == "run" &&
    bundle.methodSignature == "run(uint256)" && bundle.selector == "0xa444f5e9" &&
    bundle.deployPath == ["SynthesizedModulesDeploy"] &&
    bundle.runtimePath == ["SynthesizedModulesDeploy", "SynthesizedModules"] &&
    Modules.version == "core-module-composition-plan-v1" &&
    Solcore.Synthesis.Source.Modules.emitterVersion == "solcore-source-modules-v2" &&
    Solcore.Synthesis.Source.Modules.wrapperVersion == "solcore-word-modules-contract-v1")
    "module provenance or contract metadata changed"

def testSourceModuleEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceModuleEmitter
