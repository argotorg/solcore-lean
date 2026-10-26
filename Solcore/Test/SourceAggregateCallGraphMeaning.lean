import Solcore.Synthesis.Source.ScalarMeaning.AggregateCallGraphEmitter
import Solcore.Test.SourceAggregateCallGraphEmitter
import Solcore.Test.SourceScalarMeaning

/-! Executable checks of the source meaning on actual aggregate call-graph
emitter output. Each emitted text is lexed, parsed and run under the
independent source semantics, then compared with the original Core binding
chain on the Core machine. `AggregateCallGraph.emit_source_meaning` covers
every successful emission; these checks exercise the same definitions, the
tokenizer and the unconditional alias import on real texts, and observe that
the final Core store is empty, which the theorem leaves existential. -/
set_option autoImplicit false

namespace Tests.SourceAggregateCallGraphMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns. The renderer refuses cells, so the final store
must be empty. -/
private def coreWord (label : String) (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      ensure store.isEmpty s!"aggregate call-graph Core run left a cell: {label}"
      pure word.val
  | _ => throw (IO.userError s!"Core reference did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checked (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr) :
    IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers entry with
  | some graph => pure graph
  | none => throw (IO.userError s!"aggregate call-graph fixture failed its checker: {label}")

private def emitted (label : String) (graph : CheckedDAG) : IO EmittedProgram :=
  match AggregateCallGraph.emit graph with
  | .ok value => pure value
  | .error error =>
      throw (IO.userError s!"aggregate call-graph emission failed: {label}: {reprStr error}")

/-- The emitted text parses to a file whose printing is that text, with one free
function per helper and the raw opcode aliases always imported. -/
private def checkReprint (label : String) (graph : CheckedDAG) (source : String) : IO Unit := do
  let some file := parseSource source |
    throw (IO.userError s!"emitted aggregate call-graph source is outside the fragment: {label}")
  ensure (file.print == source)
    s!"parsed aggregate call-graph source does not print back: {label}"
  ensure (file.opcodeAliases == primitiveAliases &&
      file.functions.length == graph.helpers.length &&
      file.contract == AggregateCallGraph.contractName)
    s!"aggregate call-graph file has other aliases, helpers or contract: {label}"

/-- Every boundary input, and every input with a hand-known result, agrees with
Core; a hand-known formula must agree as well. Returns the emitted text. -/
private def checkGraph (label : String) (graph : CheckedDAG) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label graph
  checkReprint label graph program.source
  for input in known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs do
    let expected ← coreWord label (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate call-graph source meaning differs from Core: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"aggregate call-graph Core result differs from its formula: {label} at {input}"
  for (input, expected) in known do
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate call-graph source differs from its hand-known result: {label} at {input}"
  ensure (sourceCall program.source "run" [2 ^ 256] == none)
    s!"aggregate call-graph method accepted an argument outside uint256: {label}"
  return program.source

/-- The nine minimal composition shapes of `SourceAggregateCallGraphEmitter` and
its scalar, adjacent and outer-local graphs, over the identity helper, with
hand-known results. -/
private def shapeFixtures : List (String × Wire.Expr × (Nat → Nat)) := [
  ("pair-component-call", .first (.pair (call 1 (.var 0)) (word 2)), fun input => input),
  ("sum-payload-call", .letE (.inRight .word (call 1 (.var 0))) (word 3), fun _ => 3),
  ("projected-call-argument", .letE (.pair (.var 0) (word 1)) (call 2 (.second (.var 0))),
    fun _ => 1),
  ("case-scrutinee-call", .caseE (.ifE (.binary .wordEq (call 1 (.var 0)) (word 0))
      (.inLeft .word (word 1)) (.inRight .word (word 2))) (.var 0) (word 7),
    fun input => if input == 0 then 1 else 7),
  ("case-branch-call", .caseE (.inLeft .word (.var 0)) (call 2 (.var 1)) (word 0),
    fun input => input),
  ("payload-call-argument", .letE (call 1 (.var 0))
      (.caseE (.inRight .word (.var 0)) (word 0) (call 3 (.var 0))),
    fun input => input),
  ("aggregate-let", .letE (.inLeft .word (.var 0)) (call 2 (.var 1)), fun input => input),
  ("aggregate-branch", .letE (call 1 (.var 0))
      (.first (.ifE (.bool true) (.pair (.var 0) (word 1)) (.pair (word 2) (.var 0)))),
    fun input => input),
  ("nested-case", .letE (call 1 (.var 0))
      (.caseE (.inLeft .word (.var 0)) (.caseE (.inRight .word (.var 0)) (.var 0) (.var 1))
        (word 0)),
    fun input => input),
  ("scalar-call", call 1 (.var 0), fun input => input),
  ("adjacent-call", .binary .wordAdd (call 1 (.var 0)) (.first (.pair (.var 0) (word 1))),
    fun input => wrap (2 * input)),
  ("outer-local", .caseE (.inLeft .word (word 1)) (call 2 (.var 1)) (word 0),
    fun input => input)]

/-- Raw opcodes applied to helper results, with the hand-known results of the
call-graph checks in `SourceScalarMeaning`. -/
private def primitiveBodies : List (String × Wire.Expr × Nat × Nat) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0)), 0, 256),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2)), 5, 2),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0)), maximum, 0),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0)), 255, high),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0)), 256, 0),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0)), maximum, maximum),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum)), high, high),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2)), maximum - 6, maximum),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0), high - 1, 1),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234)), 31, 0x34),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0)), maximum, maximum),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0)), 0x80, maximum - 0x7f),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum)), maximum, 1),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)), high, 1)]

/-- A Word placed in a pair and projected back, or carried as a right payload
and returned from its case. -/
private def aggregateWrappers : List (String × (Wire.Expr → Wire.Expr)) := [
  ("projected", fun body => .first (.pair body (.var 0))),
  ("payload", fun body => .caseE (.inRight .word body) (word 0) (.var 0))]

/-- Generated graphs from the `runtime-aggregate-call-graphs` generator, which
together cover every composition shape. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut shapes : List String := []
  for budget in [96, 192, 256] do
    for seed in List.range 8 do
      match AggregateCallGraph.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
      | .error error => throw (IO.userError
          s!"aggregate call-graph generator failed at seed {seed}: {reprStr error}")
      | .ok generated =>
          let graph := generated.function
          let _ ← checkGraph s!"generated budget {budget} seed {seed}" graph
          shapes := (shapes ++ AggregateCallGraph.structuralShapes graph).eraseDups
          count := count + 1
  ensure (AggregateCallGraph.shapeCatalog.all shapes.contains)
    "generated aggregate call graphs missed a composition shape"
  return count

/-- Texts outside the fragment, or without a meaning, are rejected rather than
given a default value. -/
private def checkRejections (shapesSource payloadSource primitiveSource : String) :
    IO Unit := do
  let swapped := payloadSource.replace "case inl(" "case inr("
  ensure (swapped != payloadSource) "payload fixture has no left case"
  ensure (parseSource swapped).isNone "a sum match with two right cases was accepted"
  let escaped := payloadSource.replace "return uint256(sc_v2);" "return uint256(sc_p5);"
  ensure (escaped != payloadSource) "payload fixture changed its result name"
  ensure ((parseSource escaped).isSome && sourceCall escaped "run" [1] == none)
    "a case payload received a meaning after its case"
  let paired := shapesSource.replace "let sc_v12: word = (sc_v6 + sc_v9);"
    "let sc_v12: word = sc_fn0(sc_v4);"
  ensure (paired != shapesSource) "all-shapes fixture changed its second helper"
  ensure ((parseSource paired).isSome && sourceCall paired "run" [1] == none)
    "a helper applied to a pair received a meaning"
  let pairResult := shapesSource.replace "    return sc_v12;" "    return sc_v4;"
  ensure (pairResult != shapesSource) "all-shapes fixture changed its second helper result"
  ensure ((parseSource pairResult).isSome && sourceCall pairResult "run" [1] == none)
    "a helper that returns a pair for a word received a meaning"
  match shapesSource.splitOn "\n\n" with
  | [imports, first, second, contract] =>
      let reordered := "\n\n".intercalate [imports, second, first, contract]
      ensure ((parseSource reordered).isSome && sourceCall reordered "run" [1] == none)
        "a helper that calls a later helper received a meaning"
  | _ => throw (IO.userError "all-shapes fixture no longer has two helpers")
  let stripped := primitiveSource.replace (Primitive.opcodeImport ++ "\n") ""
  ensure (stripped != primitiveSource) "primitive fixture has no alias import"
  ensure ((parseSource stripped).isSome && sourceCall stripped "run" [1] == none)
    "a primitive text without its alias import received a meaning"

def testSourceAggregateCallGraphMeaning : IO Unit := do
  let shapes ← checked "all shapes" Tests.SourceAggregateCallGraphEmitter.allShapesHelpers
    Tests.SourceAggregateCallGraphEmitter.allShapesEntry
  -- x > 5: 8x + 4 through the left payload; otherwise 4x + 1 through the right.
  let shapesSource ← checkGraph "all shapes" shapes
    (formula := some fun input => if input > 5 then wrap (8 * input + 4) else 4 * input + 1)
  for (label, entry, formula) in shapeFixtures do
    let _ ← checkGraph label (← checked label [.var 0] entry) (formula := some formula)
  let projected ← checked "projected call pair" [.var 0]
    (.first (.pair (call 1 (.var 0)) (.var 0)))
  let _ ← checkGraph "projected call pair" projected [(9, 9)] (some fun input => input)
  let payload ← checked "payload helper call" [.binary .wordAdd (.var 0) (word 1)]
    (.letE (.inRight .word (.var 0)) (.caseE (.var 0) (word 0) (call 3 (.var 0))))
  let payloadSource ← checkGraph "payload helper call" payload [(41, 42)]
    (some fun input => wrap (input + 1))
  let mixed ← checked "call-graph mixed" Tests.SourceCallGraphEmitter.mixedHelpers
    Tests.SourceCallGraphEmitter.mixedEntry
  let _ ← checkGraph "call-graph mixed" mixed [(0, 11), (1, 6), (maximum, 1), (high, high / 2)]
  let mut primitiveSource := ""
  for (wrapper, aggregate) in aggregateWrappers do
    for (label, body, input, expected) in primitiveBodies do
      let graph ← checked s!"{wrapper} {label}" [.var 0] (aggregate body)
      let source ← checkGraph s!"{wrapper} {label}" graph [(input, expected)]
      if primitiveSource.isEmpty then primitiveSource := source
  let generated ← checkGenerated
  checkRejections shapesSource payloadSource primitiveSource
  IO.println (s!"aggregate call-graph source meaning: the all-shapes graph, " ++
    s!"{shapeFixtures.length} shape fixtures, 3 call fixtures, " ++
    s!"{aggregateWrappers.length * primitiveBodies.length} raw primitive bodies and " ++
    s!"{generated} generated graphs x {Tests.SourceScalarMeaning.boundaryInputs.length} " ++
    "inputs agree with Core")

end Tests.SourceAggregateCallGraphMeaning
