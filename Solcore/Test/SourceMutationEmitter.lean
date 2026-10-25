import Solcore.Synthesis.Source.MutationEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Mutable-local regressions: reads snapshot before later writes, elided Unit
binders retain their indices, and cells do not alias across bindings or calls.
The independent Core result remains the oracle for subsequent Rust/EVM tests. -/
set_option autoImplicit false

namespace Tests.SourceMutationEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.LocalMutation (CheckedDAG)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)

/-- With input one, the original Core computes one plus two, not two plus two. -/
def snapshotBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.binary .wordAdd (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))

def twoCellsBody : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.letE (.newCell .word (word 10))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 1)))
      (.binary .wordAdd (.loadCell (.var 2)) (.loadCell (.var 1)))))

def isolationBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.apply (.var 2) (.loadCell (.var 0)))
      (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 1)))
        (.binary .wordAdd (.var 1) (.loadCell (.var 2)))))

def unitBeforeCallBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (word 9))
      (.letE (.apply (.var 3) (.loadCell (.var 1)))
        (.binary .wordAdd (.var 0) (.loadCell (.var 2)))))

def boolAndUnitBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.binary .wordGt (.loadCell (.var 0)) (word 0))
      (.letE (.ifE (.var 0)
        (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (word 1))) .unit)
        (.loadCell (.var 2))))

def nestedStoreBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0)
      (.letE (.storeCell (.var 0) (word 2))
        (.binary .wordAdd (.loadCell (.var 1)) (word 3))))
      (.loadCell (.var 1)))

def fixtures : List (String × List Wire.Expr × Wire.Expr) := [
  ("load-before-store", [snapshotBody], entry),
  ("independent-cells", [twoCellsBody], entry),
  ("callee-isolation", [snapshotBody, isolationBody], entry),
  ("unit-before-call", [snapshotBody, unitBeforeCallBody], entry),
  ("bool-and-unit", [boolAndUnitBody], entry),
  ("nested-store-value", [nestedStoreBody], entry)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "mutation fixture failed checked profile admission")

private def emitted (graph : CheckedDAG) : IO EmittedProgram :=
  match Mutation.emit graph with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"mutation emission failed: {reprStr error}")

private def observe (graph : CheckedDAG) (input expected : Nat) : IO Unit := do
  let applied := graph.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied mutation graph failed Core typing"
  match applied.toCore.runStateful 3000 with
  | .done (.word value) _ => ensure (value.val == expected) "independent Core mutation result changed"
  | _ => throw (IO.userError "independent Core mutation graph did not return a Word")

private def admissionChecks : IO Unit := do
  for (label, helpers, body) in fixtures do
    let graph ← checked helpers body
    ensure graph.program.check s!"mutation graph escaped full Core checking: {label}"
    let some restored := CheckedDAG.ofProgram? graph.program |
      throw (IO.userError s!"mutation graph failed canonical readmission: {label}")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
      "mutation graph readmission changed its original Core"
    let source ← emitted graph
    ensure (source == (← emitted graph)) "mutation emission is not deterministic"
    ensure (source.contractName == "SynthesizedMutation" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedMutationDeploy"] &&
      source.runtimePath == ["SynthesizedMutationDeploy", "SynthesizedMutation"])
      "mutation wrapper metadata changed"
  let aliasBody : Wire.Expr := .letE (.newCell .word (.var 0))
    (.letE (.var 0) (.loadCell (.var 0)))
  ensure (functionDAGProgram [aliasBody] entry).check
    "alias rejection stopped exercising an otherwise well-typed Core graph"
  for body in [aliasBody,
      .loadCell (.newCell .word (.var 0)),
      .letE (.newCell .word (.var 0))
        (.loadCell (.ifE (.bool true) (.var 0) (.var 0))),
      .letE (.newCell .word (.var 0)) (.var 0),
      .letE (.newCell .bool (.bool false)) (word 0),
      .letE (.storeCell (.var 0) (word 1)) (.var 1),
      .letE (.newCell .word (.var 0)) (.letE .unit (.loadCell (.var 0))),
      .apply (.var 1) (.var 0)] do
    ensure (CheckedDAG.ofParts? [body] entry).isNone
      "mutation profile admitted an alias, escape, indirect reference, wrong kind or host call"
  ensure (CheckedDAG.ofParts? [] (.var 0)).isNone "empty mutation helper graph was admitted"
  ensure (CheckedDAG.ofParts? (List.replicate 4 snapshotBody) entry).isNone
    "mutation helper count exceeded its bound"
  ensure (LocalMutation.infer? [.unit, .cellWord, .word] 1 (.loadCell (.var 1)) == some .word &&
    LocalMutation.infer? [.unit, .cellWord, .word] 1 (.var 0) == some .unit &&
    LocalMutation.infer? [.unit, .cellWord, .word] 1 (.var 1) == none)
    "typed context erased a Unit index or exposed a cell value"

private def executionChecks : IO Unit := do
  let snapshot ← checked [snapshotBody]
  let independent ← checked [twoCellsBody]
  let isolated ← checked [snapshotBody, isolationBody]
  let sequenced ← checked [snapshotBody, unitBeforeCallBody]
  let branches ← checked [boolAndUnitBody]
  let nested ← checked [nestedStoreBody]
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do
    observe snapshot input (Word.ofNatModulo (input + 2)).val
    observe independent input (Word.ofNatModulo (input + 11)).val
    observe isolated input (Word.ofNatModulo (2 * input + 3)).val
    observe sequenced input 20
    observe branches input (if input == 0 then 0 else (Word.ofNatModulo (input + 1)).val)
    observe nested input 5
  observe snapshot 1 3
  match (snapshot.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was treated as a completed mutation")
  let unsupported : Wire.Expr := .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordDiv (.loadCell (.var 0)) (word 0)))
      (.loadCell (.var 1)))
  match Mutation.emit (← checked [unsupported]) with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "unsupported mutation arithmetic was silently emitted")

private def snapshotExpected : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_c0: word = sc_arg;",
  "    let sc_v1: word = sc_c0;",
  "    let sc_v2: word = 2;",
  "    sc_c0 = sc_v2;",
  "    let sc_v3: word = sc_c0;",
  "    let sc_v4: word = (sc_v1 + sc_v3);",
  "    return sc_v4;", "}", "",
  "contract SynthesizedMutation {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_v0: word = sc_fn0(sc_input);",
  "        return uint256(sc_v0);", "    }", "}", ""]

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  ensure ((← emitted (← checked [snapshotBody])).source == snapshotExpected)
    "cell read was not snapshotted before the following store"
  let independent ← emitted (← checked [twoCellsBody])
  ensure (contains independent.source "let sc_c0: word = sc_arg;" &&
    contains independent.source "let sc_c2: word = sc_v1;" &&
    contains independent.source "sc_c0 = sc_v5;" &&
    !contains independent.source "sc_c2 =") "independent cells shared a mutable source binding"
  let isolated ← emitted (← checked [snapshotBody, isolationBody])
  let callAndRead := String.intercalate "\n" [
    "    let sc_v2: word = sc_fn0(sc_v1);", "    let sc_v3: word = sc_v2;",
    "    let sc_v4: word = sc_c0;"]
  ensure (contains isolated.source callAndRead) "callee mutation was substituted for the caller's own cell"
  let sequence ← emitted (← checked [snapshotBody, unitBeforeCallBody])
  ensure (contains sequence.source "let sc_v3: word = sc_fn0(sc_v2);" &&
    !contains sequence.source ": unit") "Unit sequencing shifted a helper or emitted a fake scalar binding"
  let branch ← emitted (← checked [boolAndUnitBody])
  ensure (contains branch.source ": bool =" && contains branch.source "} else {\n    }" &&
    !contains branch.source ": unit") "Unit branches lost their statement-only source shape"
  let graph ← checked [snapshotBody]
  for feature in ["newCell", "loadCell", "storeCell", "functionCall"] do
    ensure (graph.features.contains feature) s!"missing mutation AST feature {feature}"
  ensure (Mutation.emitterVersion == "solcore-source-mutation-v1" &&
    Mutation.wrapperVersion == "solcore-word-mutation-contract-v1" &&
    Mutation.selector == "0xa444f5e9" && LocalMutation.version == "core-local-mutation-dag-v1")
    "mutation provenance changed"

def testSourceMutationEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceMutationEmitter
