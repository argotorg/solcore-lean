import Solcore.Synthesis.Source.AggregateEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Internal aggregates preserve evaluation order and immutable snapshots while
case payloads, Unit sequencing, cells and earlier helpers share Core indices.
These tests check the original Core oracle and the emitted statement structure;
Rust/EVM differential execution exercises the actual source compiler separately. -/
set_option autoImplicit false

namespace Tests.SourceAggregateEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
def entry : Wire.Expr := .apply (.var 1) (.var 0)

/-- The left field snapshots the input, the right field writes two, and a later
write of nine must not alter either field. Input one therefore returns three. -/
def pairSnapshotBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.pair (.loadCell (.var 0))
      (.letE (.storeCell (.var 0) (word 2)) (.loadCell (.var 1))))
      (.letE (.storeCell (.var 1) (word 9))
        (.binary .wordAdd (.first (.var 1)) (.second (.var 1)))))

/-- Each field increments the cell. Projection must evaluate this pair once. -/
def projectionOnceBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.first (.pair
      (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1)))
        (.loadCell (.var 1)))
      (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1)))
        (.loadCell (.var 1)))))
      (.binary .wordAdd (.var 0) (.loadCell (.var 1))))

def sumSnapshotBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inRight .word (.loadCell (.var 0))) (.inLeft .word (.loadCell (.var 0))))
      (.letE (.storeCell (.var 1) (word 9))
        (.caseE (.var 1)
          (.binary .wordAdd (.var 0) (.loadCell (.var 3)))
          (.binary .wordAdd (.binary .wordAdd (.var 0) (word 1))
            (.loadCell (.var 3))))))

/-- The payload shifts both a caller cell and an earlier helper. The helper
allocates its own cell, so its write cannot replace the caller's saved value. -/
def payloadCallBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.caseE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inLeft .word (.var 1)) (.inRight .word (.var 1)))
      (.letE (.binary .wordAdd (.var 0) (word 1))
        (.letE (.storeCell (.var 2) (.var 0))
          (.letE (.apply (.var 5) (.var 1))
            (.binary .wordAdd (.var 0) (.loadCell (.var 4))))))
      (.letE (.storeCell (.var 1) (word 5))
        (.apply (.var 4) (.loadCell (.var 2)))))

/-- Both cases return aggregates, and their payload binder shifts the saved pair. -/
def aggregateCaseBody : Wire.Expr :=
  .letE (.caseE (.ifE (.binary .wordGt (.var 0) (word 0))
    (.inRight .word (.var 0)) (.inLeft .word (.var 0)))
    (.pair (.var 0) (word 10))
    (.pair (.binary .wordAdd (.var 0) (word 1)) (word 20)))
    (.letE (.caseE (.inLeft .word (.first (.var 0)))
      (.inRight .word (.binary .wordAdd (.var 0) (.second (.var 1))))
      (.inLeft .word (.var 0)))
      (.caseE (.var 0)
        (.binary .wordAdd (.var 0) (.first (.var 2)))
        (.binary .wordAdd (.var 0) (.first (.var 2)))))

/-- Unit-valued case branches update only the selected branch's caller cell. -/
def unitCaseBody : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.caseE (.ifE (.binary .wordGt (.var 1) (word 0))
      (.inLeft .word (.var 1)) (.inRight .word (.var 1)))
      (.letE (.var 0) (.storeCell (.var 2) (.binary .wordAdd (.var 0) (word 1))))
      (.storeCell (.var 1) (word 7)))
      (.loadCell (.var 1)))

private def joinValue (target : Aggregates.Target) (left : Bool) : Wire.Expr :=
  match target with
  | .word => word (if left then 11 else 13)
  | .bool => .bool left
  | .unit => .letE (word (if left then 11 else 13)) .unit
  | .wordPair => .pair (word (if left then 11 else 13)) (word 1)
  | .wordSum => if left then .inLeft .word (word 11) else .inRight .word (word 13)

private def consume (target : Aggregates.Target) (expression : Wire.Expr) : Wire.Expr :=
  .letE expression (match target with
    | .word => .var 0
    | .bool => .ifE (.var 0) (word 11) (word 13)
    | .unit => word 17
    | .wordPair => .first (.var 0)
    | .wordSum => .caseE (.var 0) (.var 0) (.var 0))

def joinBody (target : Aggregates.Target) (useCase : Bool) : Wire.Expr :=
  let tested := Wire.Expr.binary .wordGt (.var 0) (word 0)
  consume target (if useCase then
    .caseE (.ifE tested (.inLeft .word (.var 0)) (.inRight .word (.var 0)))
      (joinValue target true) (joinValue target false)
    else .ifE tested (joinValue target true) (joinValue target false))

def fixtures : List (String × List Wire.Expr × Wire.Expr) := [
  ("pair-snapshot", [pairSnapshotBody], entry),
  ("projection-once", [projectionOnceBody], entry),
  ("sum-snapshot", [sumSnapshotBody], entry),
  ("payload-helper-isolation", [pairSnapshotBody, payloadCallBody], entry),
  ("aggregate-case-joins", [aggregateCaseBody], entry),
  ("unit-case-effects", [unitCaseBody], entry)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "aggregate fixture failed checked profile admission")

private def emitted (graph : CheckedDAG) : IO EmittedProgram :=
  match Aggregate.emit graph with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")

private def observe (graph : CheckedDAG) (input expected : Nat) : IO Unit := do
  let applied := graph.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied aggregate graph failed Core typing"
  match applied.toCore.runStateful 5000 with
  | .done (.word value) _ =>
      ensure (value.val == expected) s!"independent Core aggregate result changed: input {input}, expected {expected}, got {value.val}"
  | _ => throw (IO.userError "independent Core aggregate graph did not return a Word")

private def admissionChecks : IO Unit := do
  for (label, helpers, body) in fixtures do
    let graph ← checked helpers body
    ensure graph.program.check s!"aggregate graph escaped full Core checking: {label}"
    let some restored := CheckedDAG.ofProgram? graph.program |
      throw (IO.userError s!"aggregate graph failed canonical readmission: {label}")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
      "aggregate graph readmission changed its original Core"
    let source ← emitted graph
    ensure (source == (← emitted graph)) "aggregate emission is not deterministic"
    ensure (source.contractName == "SynthesizedAggregates" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedAggregatesDeploy"] &&
      source.runtimePath == ["SynthesizedAggregatesDeploy", "SynthesizedAggregates"])
      "aggregate wrapper metadata changed"
  let nestedPair := Wire.Expr.letE (.pair (.pair (word 1) (word 2)) (word 3)) (word 0)
  let aggregateCell := Wire.Expr.letE (.newCell (.product .word .word)
    (.pair (word 1) (word 2))) (word 0)
  ensure ((functionDAGProgram [nestedPair] entry).check &&
    (functionDAGProgram [aggregateCell] entry).check)
    "aggregate rejection stopped exercising otherwise well-typed Core graphs"
  for body in [nestedPair, aggregateCell,
      .letE (.inLeft .bool (word 1)) (word 0),
      .letE (.inRight .word (.pair (word 1) (word 2))) (word 0),
      .letE (.newCell .word (.var 0)) (.letE (.var 0) (word 0)),
      .letE (.newCell .word (.var 0)) (.pair (.var 0) (word 1)),
      .letE (.newCell .word (.var 0)) (.caseE (.inLeft .word (word 1)) (.var 1) (.var 1)),
      .caseE (.inLeft .word (word 1)) (.var 0) (.bool true),
      .letE (.newCell .word (.var 0))
        (.caseE (.inLeft .word (word 1)) (.loadCell (.var 0)) (.loadCell (.var 1))),
      .apply (.var 1) (.var 0),
      .letE (.lambda .word .word (.var 0)) (.apply (.var 0) (word 1))] do
    ensure (CheckedDAG.ofParts? [body] entry).isNone
      "aggregate profile admitted a nested type, alias, escape, wrong payload scope or indirect call"
  ensure (CheckedDAG.ofParts? [] (.var 0)).isNone "empty aggregate helper graph was admitted"
  ensure (CheckedDAG.ofParts? (List.replicate 4 pairSnapshotBody) entry).isNone
    "aggregate helper count exceeded its bound"
  ensure (Aggregates.infer? [.word, .unit, .wordPair, .wordSum, .cellWord, .word] 1
      (.binary .wordAdd (.first (.var 2)) (.loadCell (.var 4))) == some .word)
    "mixed payload/Unit/aggregate/cell context changed its indices"

private def executionChecks : IO Unit := do
  let pair ← checked [pairSnapshotBody]
  let projection ← checked [projectionOnceBody]
  let sum ← checked [sumSnapshotBody]
  let isolated ← checked [pairSnapshotBody, payloadCallBody]
  let aggregates ← checked [aggregateCaseBody]
  let unit ← checked [unitCaseBody]
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do
    observe pair input (Word.ofNatModulo (input + 2)).val
    observe projection input (Word.ofNatModulo (2 * input + 3)).val
    observe sum input (Word.ofNatModulo (input + if input == 0 then 9 else 10)).val
    observe isolated input (if input == 0 then 7 else (Word.ofNatModulo (2 * input + 4)).val)
    observe aggregates input (if input == 0 then 10 else (Word.ofNatModulo (2 * input + 22)).val)
    observe unit input (if input == 0 then 7 else (Word.ofNatModulo (input + 1)).val)
  observe pair 1 3
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let graph ← checked [joinBody target useCase]
      let _ ← emitted graph
      for input in [0, 1, Word.maximum.val, 2 ^ 255] do
        observe graph input (if target == .unit then 17 else if input == 0 then 13 else 11)
  match (pair.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel was treated as a completed aggregate computation")
  let unsupported := Wire.Expr.caseE (.inLeft .word (.var 0))
    (.binary .wordDiv (.var 0) (word 1)) (.var 0)
  match Aggregate.emit (← checked [unsupported]) with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "unsupported aggregate arithmetic was silently emitted")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def pairSnapshotExpected : String := String.intercalate "\n" [
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_c0: word = sc_arg;",
  "    let sc_v1: word = sc_c0;",
  "    let sc_v2: word = 2;",
  "    sc_c0 = sc_v2;",
  "    let sc_v3: word = sc_c0;",
  "    let sc_v4: (word, word) = (sc_v1, sc_v3);",
  "    let sc_v5: (word, word) = sc_v4;",
  "    let sc_v6: word = 9;",
  "    sc_c0 = sc_v6;",
  "    let sc_v7: word = 0;",
  "    match (sc_v5) {",
  "        case (sc_p8, sc_p9) {",
  "            sc_v7 = sc_p8;",
  "        }", "    }",
  "    let sc_v10: word = 0;",
  "    match (sc_v5) {",
  "        case (sc_p11, sc_p12) {",
  "            sc_v10 = sc_p12;",
  "        }", "    }",
  "    let sc_v13: word = (sc_v7 + sc_v10);",
  "    return sc_v13;", "}"]

private def formattingChecks : IO Unit := do
  ensure (contains (← emitted (← checked [pairSnapshotBody])).source pairSnapshotExpected)
    "aggregate snapshot or tuple projection rendering changed"
  let projection ← emitted (← checked [projectionOnceBody])
  ensure ((projection.source.splitOn "sc_c0 =").length == 3)
    "projection evaluated an effectful operand more than once"
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let output ← emitted (← checked [joinBody target useCase])
      ensure (!contains output.source ": unit") "Unit join introduced a fake value binding"
      if useCase then
        ensure (contains output.source "case inl(sc_p" && contains output.source "case inr(sc_p")
          "sum match omitted a fresh payload branch"
      match target with
      | .bool => ensure (contains output.source ": bool = false;") "Bool join omitted its typed default"
      | .wordPair =>
        ensure (contains output.source ": (word, word) = (0, 0);")
          "pair join omitted its typed default"
      | .wordSum =>
        ensure (contains output.source ": sum<word, word> = inl(0);")
          "sum join omitted its typed default"
      | _ => pure ()
  let graph ← checked [aggregateCaseBody]
  for feature in ["pair", "first", "second", "inLeft", "inRight", "case", "functionCall"] do
    ensure (graph.features.contains feature) s!"missing aggregate AST feature {feature}"
  ensure (Aggregate.emitterVersion == "solcore-source-aggregates-v1" &&
    Aggregate.wrapperVersion == "solcore-word-aggregates-contract-v1" &&
    Aggregate.selector == "0xa444f5e9" && Aggregates.version == "core-aggregate-dag-v1")
    "aggregate provenance changed"

def testSourceAggregateEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceAggregateEmitter
