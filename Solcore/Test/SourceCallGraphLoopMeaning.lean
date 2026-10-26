import Solcore.Synthesis.Source.ScalarMeaning.CallGraphLoopEmitter
import Solcore.Test.SourceCallGraphEmitter
import Solcore.Test.SourceScalarMeaning

/-! Executable checks of the loop meaning on actual call-graph loop emitter
output. Each emitted text is lexed, parsed with the loop grammar and run under
the fuel-indexed source semantics, then compared with the original Core
bounded loop on the Core machine. `CallGraphLoop.emit_source_meaning` covers
every successful emission; these checks exercise the same definitions on real
texts. They also observe the exact fuel each loop needs, that the final Core
store is the accumulator cell holding the result (the theorem leaves the store
existential), that loop-free texts keep their `sourceCall` meaning, and that
altered loops lose or change their meaning. -/
set_option autoImplicit false

namespace Tests.SourceCallGraphLoopMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.CallGraphLoop (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns. The final store must be the one accumulator
cell, holding that Word. -/
private def coreWord (label : String) (program : Program) : IO Nat :=
  match program.runStateful 100000 with
  | .done (.word word) [.word cell] => do
      ensure (cell == word) s!"call-graph loop accumulator differs from its result: {label}"
      pure word.val
  | _ => throw (IO.userError s!"Core loop did not return a Word with one cell: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

/-- `count` applications of `step`. -/
private def iterate (step : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | count + 1, value => iterate step count (step value)

private def checkedPlan (label : String) (helpers : List Wire.Expr) (entry : Wire.Expr)
    (mask : Nat) : IO CheckedPlan := do
  let some graph := CheckedWordFunctionDAG.ofParts? helpers entry |
    throw (IO.userError s!"call-graph loop step failed its checker: {label}")
  let some plan := CheckedPlan.ofParts? graph mask |
    throw (IO.userError s!"call-graph loop plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match CallGraphLoop.emit plan with
  | .ok value => pure value
  | .error error =>
      throw (IO.userError s!"call-graph loop emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the loop grammar to a file whose printing is
that text, with the raw aliases, one free function per helper and `sc_step`
last. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLoopSource source |
    throw (IO.userError s!"emitted call-graph loop source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed call-graph loop source does not print back: {label}"
  ensure (file.opcodeAliases == primitiveAliases &&
      file.functions.length == plan.graph.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == CallGraphLoop.contractName)
    s!"call-graph loop file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone
    s!"the loop-free grammar accepted a call-graph loop text: {label}"

/-- Every boundary input, the iteration counts three, six and seven, and every
input with a hand-known result agree with Core once the loop has one more unit
of fuel than iterations; less fuel has no meaning. A hand-known formula must
agree as well. Returns the emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) : IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let inputs := known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs ++ [3, 6, 7]
  for input in inputs do
    let expected ← coreWord label (plan.instantiate (Word.ofNatModulo input)).toCore
    let iterations := input &&& plan.mask
    for fuel in [iterations + 1, plan.mask + 1, 64] do
      ensure (loopSourceCall fuel program.source "run" [input] == some expected)
        s!"call-graph loop source meaning differs from Core: {label} at {input}, fuel {fuel}"
    ensure (loopSourceCall iterations program.source "run" [input] == none)
      s!"call-graph loop finished with fewer condition evaluations: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a call-graph loop a result: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"call-graph loop Core result differs from its formula: {label} at {input}"
  for (input, expected) in known do
    ensure (loopSourceCall (plan.mask + 1) program.source "run" [input] == some expected)
      s!"call-graph loop source differs from its hand-known result: {label} at {input}"
  ensure (loopSourceCall 64 program.source "run" [2 ^ 256] == none)
    s!"call-graph loop method accepted an argument outside uint256: {label}"
  return program.source

/-- Raw opcodes applied to helper results, with the hand-known results of one
application from `SourceAggregateCallGraphMeaning`. Under mask one, an odd input
applies the step once and an even input returns unchanged. -/
private def primitiveSteps : List (String × Wire.Expr × Nat × Nat) :=
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

/-- Plans from the `runtime-call-graph-loops` generator, which together use
every generated mask. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut masks : List Nat := []
  for budget in [128, 256, 512] do
    for seed in List.range 8 do
      match CallGraphLoop.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
      | .error error => throw (IO.userError
          s!"call-graph loop generator failed at seed {seed}: {reprStr error}")
      | .ok generated =>
          let _ ← checkPlan s!"generated budget {budget} seed {seed}" generated.plan
          masks := (masks ++ [generated.plan.mask]).eraseDups
          count := count + 1
  ensure (CallGraphLoop.generatedMasks.all masks.contains)
    "generated call-graph loops missed a mask"
  return count

/-- On loop-free emitted texts, the loop grammar returns the same file and the
loop meaning is `sourceCall` for every fuel. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  let some mixed := CheckedWordFunctionDAG.ofParts? Tests.SourceCallGraphEmitter.mixedHelpers
      Tests.SourceCallGraphEmitter.mixedEntry |
    throw (IO.userError "mixed call graph failed its checker")
  let some clz := CheckedWordFunctionDAG.ofParts? [.var 0] (.unary .wordClz (call 1 (.var 0))) |
    throw (IO.userError "clz call graph failed its checker")
  for graph in [mixed, clz] do
    let program ← match CallGraph.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"call-graph emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted call-graph source is outside the loop-free fragment")
    let some loopFile := parseLoopSource program.source |
      throw (IO.userError "the loop grammar rejected a loop-free text")
    ensure (loopFile.print == program.source && file.toLoop.print == program.source)
      "the loop grammar changed a loop-free file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      for fuel in [0, 1, 64] do
        ensure (loopSourceCall fuel program.source "run" [input] ==
            sourceCall program.source "run" [input])
          s!"loop meaning differs from sourceCall on a loop-free text at {input}, fuel {fuel}"
    count := count + 1
  return count

/-- Altered loops lose their meaning or change their result. -/
private def checkAlterations (source : String) (plan : CheckedPlan) : IO Unit := do
  let core (input : Nat) : IO Nat := coreWord "altered"
    (plan.instantiate (Word.ofNatModulo input)).toCore
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"loop fixture has no {old}"
    pure changed
  let doubled ← replace "while (sc_limit > sc_counter) {" "while ((sc_limit > sc_counter)) {"
  ensure (parseLoopSource doubled).isNone "a loop condition in two parentheses was accepted"
  let endless ← replace "            sc_counter = (sc_counter + 1);\n" ""
  ensure ((parseLoopSource endless).isSome &&
      loopSourceCall 1000 endless "run" [0] == some (← core 0) &&
      loopSourceCall 1000 endless "run" [7] == none)
    "a loop without its counter step received a meaning"
  let shadowed ← replace "            sc_acc = sc_step(sc_acc);"
    "            let sc_acc: word = sc_step(sc_acc);"
  ensure (loopSourceCall 64 shadowed "run" [7] == some 7 && (← core 7) != 7)
    "a loop body declaration outlived its iteration"
  let reversed ← replace "while (sc_limit > sc_counter) {" "while (sc_counter > sc_limit) {"
  ensure (loopSourceCall 64 reversed "run" [7] == some 7)
    "a reversed loop condition still iterated"
  let wordCondition ← replace "while (sc_limit > sc_counter) {"
    "while (sc_limit + sc_counter) {"
  ensure ((parseLoopSource wordCondition).isSome &&
      loopSourceCall 64 wordCondition "run" [0] == none)
    "a loop condition of type word received a meaning"
  let undeclared ← replace "            sc_acc = sc_step(sc_acc);"
    "            sc_next = sc_step(sc_acc);"
  ensure ((parseLoopSource undeclared).isSome &&
      loopSourceCall 64 undeclared "run" [7] == none)
    "a loop assignment to an undeclared name received a meaning"
  let stride ← replace "sc_counter = (sc_counter + 1);" "sc_counter = (sc_counter + 2);"
  ensure (loopSourceCall 64 stride "run" [7] != some (← core 7))
    "a loop counting by two still agreed with Core"

def testSourceCallGraphLoopMeaning : IO Unit := do
  let doubled ← checkedPlan "doubled" [.binary .wordAdd (.var 0) (word 1)]
    (call 1 (.binary .wordMul (.var 0) (word 2))) 7
  -- 2x + 1 applied input & 7 times; the maximum Word is a fixed point.
  let doubledSource ← checkPlan "doubled" doubled
    [(0, 0), (1, 3), (3, 31), (7, 1023), (maximum, maximum), (high, high)]
    (some fun input => iterate (fun value => wrap (2 * value + 1)) (input &&& 7) input)
  -- ((2x) >> 4) applied input & 3 times.
  let shifted ← checkedPlan "shifted" [.binary .wordShl (.var 0) (word 1)]
    (.binary .wordShr (call 1 (.var 0)) (word 4)) 3
  let _ ← checkPlan "shifted" shifted [(0xF003, 120), (257, 32)]
    (some fun input => iterate (fun value => wrap (2 * value) / 16) (input &&& 3) input)
  for mask in [0, 1, 3, 7] do
    let identity ← checkedPlan s!"identity mask {mask}" [.var 0] (call 1 (.var 0)) mask
    let _ ← checkPlan s!"identity mask {mask}" identity (formula := some fun input => input)
  for mask in [1, 7] do
    let mixed ← checkedPlan s!"mixed mask {mask}" Tests.SourceCallGraphEmitter.mixedHelpers
      Tests.SourceCallGraphEmitter.mixedEntry mask
    let known := if mask == 1 then [(0, 0), (1, 6), (maximum, 1), (high, high)] else []
    let _ ← checkPlan s!"mixed mask {mask}" mixed known
  for (label, body, input, expected) in primitiveSteps do
    let plan ← checkedPlan label [.var 0] body 1
    let _ ← checkPlan label plan [(input, if input % 2 == 1 then expected else input)]
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations doubledSource doubled
  IO.println (s!"call-graph loop source meaning: 2 closed-form plans, 4 identity masks, " ++
    s!"2 mixed plans, {primitiveSteps.length} raw primitive steps and {generated} generated " ++
    s!"plans agree with Core at their exact fuel; {loopFree} loop-free texts keep sourceCall")

end Tests.SourceCallGraphLoopMeaning
