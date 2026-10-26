import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.ScalarMeaning.AggregateEmitter
import Solcore.Test.SourceAggregateEmitter
import Solcore.Test.SourceScalarMeaning

/-! Executable checks of the source meaning on actual aggregate emitter
output. Each emitted text is lexed, parsed and run under the independent
source semantics, then compared with the original Core binding chain on the
Core machine. `Aggregate.emit_source_meaning` covers every successful
emission; these checks exercise the same definitions, the tokenizer and the
conditional alias import on real texts. -/
set_option autoImplicit false

namespace Tests.SourceAggregateMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Aggregates (CheckedDAG)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def coreWord (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) _ => pure word.val
  | _ => throw (IO.userError "Core reference did not return a Word")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def arg : Wire.Expr := .var 0
private def entry : Wire.Expr := .apply (.var 1) (.var 0)

private def checked (label : String) (helpers : List Wire.Expr) (body : Wire.Expr := entry) :
    IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError s!"aggregate fixture failed its checker: {label}")

private def emitted (label : String) (graph : CheckedDAG) : IO EmittedProgram :=
  match Aggregate.emit graph with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"aggregate emission failed: {label}: {reprStr error}")

/-- The emitted text parses to a file whose printing is that text, and the file
imports the raw opcode aliases exactly when a rendered body uses one. -/
private def checkReprint (label : String) (graph : CheckedDAG) (source : String) : IO Unit := do
  let some file := parseSource source |
    throw (IO.userError s!"emitted aggregate source is outside the parsed fragment: {label}")
  ensure (file.print == source) s!"parsed aggregate source does not print back: {label}"
  let uses := (graph.helpers ++ [graph.entry]).any AggregateRenderer.usesOpcodeAliases
  ensure (file.opcodeAliases == if uses then primitiveAliases else [])
    s!"aggregate alias import does not follow alias use: {label}"

/-- Every boundary input agrees with Core; an optional hand-known formula must
agree as well. Returns the emitted text. -/
private def checkAggregate (label : String) (graph : CheckedDAG)
    (known : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label graph
  checkReprint label graph program.source
  for input in Tests.SourceScalarMeaning.boundaryInputs do
    let expected ← coreWord (graph.instantiate (Word.ofNatModulo input)).toCore
    ensure (sourceCall program.source "run" [input] == some expected)
      s!"aggregate source meaning differs from Core: {label} at {input}"
    if let some formula := known then
      ensure (expected == formula input)
        s!"aggregate Core result differs from its hand-known result: {label} at {input}"
  ensure (sourceCall program.source "run" [2 ^ 256] == none)
    s!"aggregate method accepted an argument outside uint256: {label}"
  return program.source

private def wrap (value : Nat) : Nat := value % 2 ^ 256

/-- Hand-known results of the aggregate emitter regression fixtures, as
general formulas of the input. -/
private def knownFixtures : List (String × (Nat → Nat)) := [
  ("pair-snapshot", fun input => wrap (input + 2)),
  ("projection-once", fun input => wrap (2 * input + 3)),
  ("sum-snapshot", fun input => wrap (input + if input == 0 then 9 else 10)),
  ("payload-helper-isolation", fun input => if input == 0 then 7 else wrap (2 * input + 4)),
  ("aggregate-case-joins", fun input => if input == 0 then 10 else wrap (2 * input + 22)),
  ("unit-case-effects", fun input => if input == 0 then 7 else wrap (input + 1))]

/-- The template result of `AggregateCases` for a scalar part, as a formula. -/
private def templateResult (pattern input scalar : Nat) : Nat :=
  let high := input ≥ 2 ^ 255
  if pattern = 0 then wrap (input + scalar)
  else if pattern = 1 then (if high then input ^^^ scalar else wrap (input + scalar))
  else if pattern = 2 then wrap (input + if high then scalar + scalar else scalar)
  else wrap (input + if high then input ^^^ scalar else wrap (input + scalar))

/-- Raw primitives inside and around aggregates, so the file imports the
aliases. -/
private def primitiveBodies : List (String × Wire.Expr) := [
  ("clz", .unary .wordClz arg),
  ("addmod", .ternary .wordAddMod arg (word 3) arg),
  ("mulmod-zero", .ternary .wordMulMod (word 5) arg (word 0)),
  ("sgt-branch", .ifE (.binary .wordSgt arg (word 1)) (.binary .wordDiv arg arg) (word 0)),
  ("pair-div-shl", .letE (.pair (.binary .wordDiv arg (word 3)) (.binary .wordShl arg (word 4)))
    (.binary .wordAdd (.first (.var 0)) (.second (.var 0)))),
  ("case-sdiv-sar", .caseE (.ifE (.binary .wordSgt arg (word 0))
      (.inLeft .word (.binary .wordSdiv arg (word 7)))
      (.inRight .word (.binary .wordSar arg (word 2))))
    (.binary .wordSmod (.var 0) (word 5)) (.binary .wordByte (word 31) (.var 0))),
  ("cell-exp-signextend", .letE (.newCell .word arg)
    (.letE (.storeCell (.var 0) (.binary .wordPow (.loadCell (.var 0)) (word 3)))
      (.binary .wordSignExtend (word 0) (.loadCell (.var 1))))),
  ("shr-mod-sum", .letE (.inRight .word (.binary .wordShr arg (word 255)))
    (.caseE (.var 0) (.var 0) (.binary .wordMod (.var 0) (word 2))))] ++
  ([Wire.BinaryOp.wordDiv, .wordMod, .wordShl, .wordShr, .wordSar, .wordSdiv, .wordSmod,
    .wordByte, .wordPow, .wordSignExtend].map fun operation =>
      (reprStr operation, .binary operation arg (word 255)))

/-- Generated aggregate graphs from the `runtime-aggregates` generator. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  for seed in List.range 24 do
    match Aggregate.generatedFunction (Seed.ofNat seed) 256 with
    | .error error => throw (IO.userError s!"aggregate generator failed at seed {seed}: {error}")
    | .ok (graph, _) =>
        let _ ← checkAggregate s!"generated seed {seed}" graph
        count := count + 1
  return count

/-- Texts outside the fragment, or without a meaning, are rejected rather than
given a default value. -/
private def checkRejections (pairSource sumSource primitiveSource : String) : IO Unit := do
  let swapped := sumSource.replace "case inl(" "case inr("
  ensure (swapped != sumSource) "sum fixture has no left case"
  ensure (parseSource swapped).isNone "a sum match with two right cases was accepted"
  let escaped := sumSource.replace "    return sc_v10;" "    return sc_p11;"
  ensure (escaped != sumSource) "sum fixture changed its result name"
  ensure ((parseSource escaped).isSome && sourceCall escaped "run" [1] == none)
    "a case payload received a meaning after its case"
  let notSum := sumSource.replace "match (sc_v8)" "match (sc_c0)"
  ensure (notSum != sumSource) "sum fixture changed its scrutinee"
  ensure ((parseSource notSum).isSome && sourceCall notSum "run" [1] == none)
    "a sum match on a word received a meaning"
  let notWord := pairSource.replace "(sc_v1, sc_v3)" "(sc_v1, true)"
  ensure (notWord != pairSource) "pair fixture changed its components"
  ensure ((parseSource notWord).isSome && sourceCall notWord "run" [1] == none)
    "a pair with a Boolean component received a meaning"
  let mistyped := pairSource.replace "sc_v7 = sc_p8;" "sc_v7 = sc_v5;"
  ensure (mistyped != pairSource) "pair fixture changed its projection"
  ensure ((parseSource mistyped).isSome && sourceCall mistyped "run" [1] == none)
    "assigning a pair to a word received a meaning"
  let unimported := pairSource.replace "(sc_v7 + sc_v10)" "sc_div(sc_v7, sc_v10)"
  ensure (unimported != pairSource) "pair fixture changed its final sum"
  ensure ((parseSource unimported).isSome && sourceCall unimported "run" [1] == none)
    "a call to an alias that is not imported received a meaning"
  let importLine := "import { " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++
    " } from std.opcodes;\n"
  let stripped := primitiveSource.replace importLine ""
  ensure (stripped != primitiveSource) "primitive fixture has no alias import"
  ensure ((parseSource stripped).isSome && sourceCall stripped "run" [1] == none)
    "a primitive text without its alias import received a meaning"

def testSourceAggregateMeaning : IO Unit := do
  let mut pairSource := ""
  let mut sumSource := ""
  for (label, helpers, body) in Tests.SourceAggregateEmitter.fixtures do
    let some (_, known) := knownFixtures.find? (·.1 == label) |
      throw (IO.userError s!"missing hand-known aggregate result: {label}")
    let source ← checkAggregate label (← checked label helpers body) known
    if label == "pair-snapshot" then pairSource := source
    if label == "sum-snapshot" then sumSource := source
  let mut joins := 0
  for target in [Aggregates.Target.word, .bool, .unit, .wordPair, .wordSum] do
    for useCase in [false, true] do
      let label := s!"join {reprStr target} {useCase}"
      let graph ← checked label [Tests.SourceAggregateEmitter.joinBody target useCase]
      let _ ← checkAggregate label graph (some fun input =>
        if target == .unit then 17 else if input == 0 then 13 else 11)
      joins := joins + 1
  for pattern in List.range 4 do
    let label := s!"template {pattern}"
    let graph ← checked label [Aggregate.template pattern (word 2)]
    let _ ← checkAggregate label graph (some fun input => templateResult pattern input 2)
  let mut primitiveSource := ""
  for (label, body) in primitiveBodies do
    let graph ← checked label [body]
    ensure (AggregateRenderer.usesOpcodeAliases body) s!"primitive body uses no alias: {label}"
    primitiveSource ← checkAggregate label graph
  let generated ← checkGenerated
  checkRejections pairSource sumSource primitiveSource
  let fixtures := Tests.SourceAggregateEmitter.fixtures.length
  IO.println (s!"aggregate source meaning: {fixtures} emitter fixtures, {joins} joins, " ++
    s!"4 templates, {primitiveBodies.length} raw primitive bodies and {generated} generated " ++
    s!"graphs x {Tests.SourceScalarMeaning.boundaryInputs.length} inputs agree with Core")

end Tests.SourceAggregateMeaning
