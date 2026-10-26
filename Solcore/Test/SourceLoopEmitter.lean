import Solcore.Synthesis.Source.LoopEmitter
import Solcore.Core.Machine

/-! The finite Core oracle and source while loop share a checked step DAG, not
a counter implementation. Regression cases cover fixed initial bounds, all
allowed masks, arbitrary entries, wrapping Words and fresh cells on every call. -/
set_option autoImplicit false

namespace Tests.SourceLoopEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)
def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)

/-- One private cell per step, with its left pair field snapshotted before the
right field overwrites the cell. Reusing a prior call's cell changes the result. -/
def mutableStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.binary .wordAdd (.first (.var 0)) (.second (.var 0))))

def arbitraryEntry : Wire.Expr := .binary .wordAdd (.apply (.var 1) (.var 0)) (word 10)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "loop step did not pass the aggregate DAG checker")

private def checked (graph : Aggregates.CheckedDAG) (mask : Nat) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph mask with
  | some plan => pure plan
  | none => throw (IO.userError "bounded loop plan failed checked admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Loop.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"loop emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, 3, 7, Word.maximum.val, 2 ^ 255]

/-- For the allowed masks, the bound is the low zero, one, two or three bits.
This arithmetic reference does not inspect or execute the generated guards. -/
private def trips (mask input : Nat) : Nat := input % (mask + 1)

private def observe (plan : CheckedPlan) (input expected : Nat)
    (expectedCells : Nat) (privateValue : Nat := 2) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied loop failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"Core loop result changed: mask {plan.mask}, input {input}, expected {expected}, got {value.val}"
      ensure (store.length == expectedCells) "loop call reused a private cell or executed the wrong number of steps"
      match (store[0]? : Option Value) with
      | some (.word accumulated) => ensure (accumulated == value) "returned accumulator differs from its cell"
      | _ => throw (IO.userError "Core loop lost its accumulator cell")
      for cell in store.drop 1 do
        match cell with
        | .word final => ensure (final.val == privateValue) "callee's private cell contents escaped between calls"
        | _ => throw (IO.userError "loop allocated a non-Word cell")
  | _ => throw (IO.userError "bounded Core loop did not return a Word")

private def admissionChecks : IO Unit := do
  let graph ← step [increment]
  for mask in [0, 1, 3, 7] do
    let plan ← checked graph mask
    ensure (plan.program.check && plan.mask == mask) "loop admission changed mask or escaped checking"
    match plan.program.body with
    | .letE saved (.lambda .word .word _) =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
          "Core loop did not bind the whole original entry closure once"
    | _ => throw (IO.userError "Core loop's closure-before-input shape changed")
    let measured := Wire.programNodes (plan.instantiate Word.maximum)
    ensure (measured == BoundedLoop.appliedNodes graph mask &&
      measured == BoundedLoop.canonicalNodes graph mask &&
      measured == Wire.programNodes graph.program + BoundedLoop.appliedOverhead mask &&
      BoundedLoop.appliedOverhead mask == 14 + 12 * mask)
      "loop node overhead differs from the complete Core program"
    let source ← emitted plan
    ensure (source == (← emitted plan)) "loop emission is nondeterministic"
    ensure (source.contractName == "SynthesizedLoops" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedLoopsDeploy"] &&
      source.runtimePath == ["SynthesizedLoopsDeploy", "SynthesizedLoops"])
      "loop wrapper metadata changed"
  for mask in [2, 4, 5, 6, 8, 15, 256, 1000000] do
    ensure (CheckedPlan.ofParts? graph mask).isNone "loop admitted an unbounded or unsupported mask"
  let mixed ← step [increment, mutableStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  for mask in [0, 1, 3, 7] do
    let plan ← checked mixed mask
    ensure (Wire.programNodes (plan.instantiate Word.zero) ==
      Wire.programNodes mixed.program + BoundedLoop.appliedOverhead mask)
      "loop overhead depends on the helper or arbitrary entry shape"

private def executionChecks : IO Unit := do
  let incrementGraph ← step [increment]
  let arbitraryGraph ← step [increment] arbitraryEntry
  let mutableGraph ← step [mutableStep]
  let mixedGraph ← step [increment, mutableStep] (.apply (.var 1) (.apply (.var 2) (.var 0)))
  let identityGraph ← step [increment] (.var 0)
  let constantGraph ← step [increment] (word 42)
  for mask in [0, 1, 3, 7] do
    let incrementPlan ← checked incrementGraph mask
    let arbitraryPlan ← checked arbitraryGraph mask
    let mutablePlan ← checked mutableGraph mask
    let mixedPlan ← checked mixedGraph mask
    let identityPlan ← checked identityGraph mask
    let constantPlan ← checked constantGraph mask
    for input in inputs do
      let count := trips mask input
      observe incrementPlan input (Word.ofNatModulo (input + count)).val 1
      observe arbitraryPlan input (Word.ofNatModulo (input + 11 * count)).val 1
      observe mutablePlan input (Word.ofNatModulo (input + 2 * count)).val (1 + count)
      observe mixedPlan input (Word.ofNatModulo (input + 3 * count)).val (1 + count)
      observe identityPlan input input 1
      observe constantPlan input (if count == 0 then input else 42) 1
  let maximum ← checked mutableGraph 7
  observe maximum 7 21 8
  observe maximum 0 0 1
  observe maximum (2 ^ 255) (2 ^ 255) 1
  match (maximum.instantiate (Word.ofNatModulo 7)).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was confused with a completed bounded loop")
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  match Loop.emit (← checked divided 0) with
  | .ok emitted => unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 && (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
      throw (IO.userError "loop emission lost the raw division alias or its operand snapshots")
  | .error error => throw (IO.userError s!"loop raw division was rejected: {reprStr error}")

private def expectedIncrement : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;",
  "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    return sc_v0;", "}", "",
  "contract SynthesizedLoops {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 3);",
  "        let sc_acc: word = sc_input;",
  "        let sc_counter: word = 0;",
  "        while (sc_limit > sc_counter) {",
  "            sc_acc = sc_step(sc_acc);",
  "            sc_counter = (sc_counter + 1);",
  "        }",
  "        return uint256(sc_acc);", "    }", "}", ""]

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [increment]
  ensure ((← emitted (← checked graph 3)).source == expectedIncrement)
    "source loop no longer uses its own counter and fixed initial bound"
  let arbitrary ← emitted (← checked (← step [increment] arbitraryEntry) 7)
  ensure (contains arbitrary.source (String.intercalate "\n" [
    "function sc_step(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);",
    "    let sc_v1: word = 10;",
    "    let sc_v2: word = (sc_v0 + sc_v1);",
    "    return sc_v2;", "}"])) "source loop ignored the arbitrary checked entry"
  ensure ((arbitrary.source.splitOn "while (").length == 2 &&
    (arbitrary.source.splitOn "sc_acc = sc_step(sc_acc);").length == 2)
    "source output unrolled or duplicated the actual while loop"
  let identity ← emitted (← checked (← step [increment] (.var 0)) 1)
  ensure (contains identity.source
    "function sc_step(sc_arg: word) returns (word) {\n    return sc_arg;\n}")
    "identity entry was replaced with the last helper"
  let mutable ← emitted (← checked (← step [mutableStep]) 7)
  ensure (contains mutable.source "function sc_fn0(sc_arg: word) returns (word) {\n    let sc_c0: word = sc_arg;" &&
    !contains mutable.source "sc_acc = sc_fn0") "private step allocation moved outside its function"
  ensure (Loop.emitterVersion == "solcore-source-loops-v2" &&
    Loop.wrapperVersion == "solcore-word-loops-contract-v1" &&
    Loop.selector == "0xa444f5e9" && BoundedLoop.version == "core-bounded-loop-plan-v1")
    "loop provenance changed"

def testSourceLoopEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceLoopEmitter
