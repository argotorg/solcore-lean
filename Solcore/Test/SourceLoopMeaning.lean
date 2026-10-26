import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.ScalarMeaning.LoopEmitter
import Solcore.Test.SourceLoopEmitter
import Solcore.Test.SourceScalarMeaning

/-! Executable checks of the loop meaning on actual aggregate loop emitter
output. Each emitted text is lexed, parsed with the loop grammar and run under
the fuel-indexed source semantics, then compared with the original Core
bounded loop on the Core machine. `Loop.emit_source_meaning` covers every
successful emission; these checks exercise the same definitions on real texts.
They also observe the exact fuel each loop needs and the final Core store,
which the theorem leaves existential: the accumulator cell comes first and
holds the result, followed by the cells the step allocated. -/
set_option autoImplicit false

namespace Tests.SourceLoopMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.BoundedLoop (CheckedPlan)
open Tests.SourceLoopEmitter (entry increment mutableStep arbitraryEntry)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns and the length of its final store. The first
location must be the accumulator cell holding the result, and every cell a
Word. -/
private def coreRun (label : String) (program : Program) : IO (Nat × Nat) :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      match store with
      | .word accumulator :: cells =>
          ensure (accumulator == word) s!"loop accumulator differs from its result: {label}"
          ensure (cells.all fun | .word _ => true | _ => false)
            s!"loop step allocated a cell that is not a Word: {label}"
      | _ => throw (IO.userError s!"Core loop lost its accumulator cell: {label}")
      pure (word.val, store.length)
  | _ => throw (IO.userError s!"Core loop did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def wrap (value : Nat) : Nat := value % 2 ^ 256
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (mask : Nat) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"loop step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? graph mask |
    throw (IO.userError s!"loop plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Loop.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"loop emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the loop grammar to a file whose printing is
that text. It imports the raw aliases exactly when a step body uses one and
declares `sc_step` after one function per helper. The loop-free grammar rejects
it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseLoopSource source |
    throw (IO.userError s!"emitted loop source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed loop source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Loop.contractName)
    s!"loop file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a loop text: {label}"

/-- Every boundary input, the inputs three, six and seven, and every input with
a hand-known result agree with Core once the loop has one more unit of fuel
than iterations; less fuel has no meaning. A hand-known formula and a
hand-known final store length, from the iteration count, must agree as well.
Returns the emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (formula : Option (Nat → Nat) := none) (cells : Option (Nat → Nat) := none) :
    IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  let inputs := known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs ++ [3, 6, 7]
  for input in inputs do
    let (expected, stored) ← coreRun label (plan.instantiate (Word.ofNatModulo input)).toCore
    let iterations := input &&& plan.mask
    for fuel in [iterations + 1, plan.mask + 1, 64] do
      ensure (loopSourceCall fuel program.source "run" [input] == some expected)
        s!"loop source meaning differs from Core: {label} at {input}, fuel {fuel}"
    ensure (loopSourceCall iterations program.source "run" [input] == none)
      s!"loop finished with fewer condition evaluations: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a loop a result: {label} at {input}"
    if let some result := formula then
      ensure (expected == result input)
        s!"loop Core result differs from its formula: {label} at {input}"
    if let some length := cells then
      ensure (stored == length iterations)
        s!"loop Core store has another number of cells: {label} at {input}"
  for (input, expected) in known do
    ensure (loopSourceCall (plan.mask + 1) program.source "run" [input] == some expected)
      s!"loop source differs from its hand-known result: {label} at {input}"
  ensure (loopSourceCall 64 program.source "run" [2 ^ 256] == none)
    s!"loop method accepted an argument outside uint256: {label}"
  return program.source

/-- The regression steps of `SourceLoopEmitter` and two steps through a
projected pair and a sum payload, with their hand-known results and cell
counts: the step runs `count` times and the store holds the accumulator and one
cell per call of the private-cell step. -/
private def fixedSteps :
    List (String × List Wire.Expr × Wire.Expr × (Nat → Nat → Nat) × (Nat → Nat)) := [
  ("increment", [increment], entry, fun input count => wrap (input + count), fun _ => 1),
  ("arbitrary entry", [increment], arbitraryEntry, fun input count => wrap (input + 11 * count),
    fun _ => 1),
  ("private cell", [mutableStep], entry, fun input count => wrap (input + 2 * count),
    fun count => 1 + count),
  ("mixed", [increment, mutableStep], .apply (.var 1) (.apply (.var 2) (.var 0)),
    fun input count => wrap (input + 3 * count), fun count => 1 + count),
  ("identity entry", [increment], .var 0, fun input _ => input, fun _ => 1),
  ("constant entry", [increment], word 42, fun input count => if count == 0 then input else 42,
    fun _ => 1),
  ("projected pair", [increment], .first (.pair (call 1 (.var 0)) (.var 0)),
    fun input count => wrap (input + count), fun _ => 1),
  ("sum payload", [increment], .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0),
    fun input count => wrap (input + count), fun _ => 1)]

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

/-- Plans from the `runtime-loops` generator at two budgets, which together
use every generated mask. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut masks : List Nat := []
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Loop.generatedPlan (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (plan, _) =>
          let _ ← checkPlan s!"generated budget {nodes} seed {seed}" plan
          masks := (masks ++ [plan.mask]).eraseDups
          count := count + 1
  ensure (count ≥ 16) s!"the loop generator produced only {count} plans"
  ensure ([1, 3, 7].all masks.contains) "generated loops missed a mask"
  return count

/-- On loop-free aggregate texts, with pairs, sums, matches and private cells,
the loop grammar returns the same file and the loop meaning is `sourceCall`
for every fuel. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  let steps := [([mutableStep], entry),
    ([increment], .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0))]
  for (helpers, body) in steps do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted aggregate source is outside the loop-free fragment")
    let some loopFile := parseLoopSource program.source |
      throw (IO.userError "the loop grammar rejected a loop-free aggregate text")
    ensure (loopFile.print == program.source && file.toLoop.print == program.source)
      "the loop grammar changed a loop-free aggregate file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      for fuel in [0, 1, 64] do
        ensure (loopSourceCall fuel program.source "run" [input] ==
            sourceCall program.source "run" [input])
          s!"loop meaning differs from sourceCall on a loop-free text at {input}, fuel {fuel}"
    count := count + 1
  return count

/-- Altered loops lose their meaning or change their result. -/
private def checkAlterations (source : String) (plan : CheckedPlan) : IO Unit := do
  let core (input : Nat) : IO Nat := do
    pure (← coreRun "altered" (plan.instantiate (Word.ofNatModulo input)).toCore).1
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
  let reused ← replace "    let sc_c0: word = sc_arg;" "    sc_c0 = sc_arg;"
  ensure ((parseLoopSource reused).isSome && loopSourceCall 64 reused "run" [7] == none)
    "a step reused a cell it never declared"

def testSourceLoopMeaning : IO Unit := do
  let mut privateSource := ""
  let mut privatePlan : Option CheckedPlan := none
  for (label, helpers, body, formula, cells) in fixedSteps do
    for mask in [0, 1, 3, 7] do
      let plan ← checkedPlan s!"{label} mask {mask}" helpers body mask
      let source ← checkPlan s!"{label} mask {mask}" plan
        (formula := some fun input => formula input (input &&& mask)) (cells := some cells)
      if label == "private cell" && mask == 7 then
        privateSource := source
        privatePlan := some plan
  -- Seven iterations of x + 2 from seven, with one fresh cell per call.
  let some sevenfold := privatePlan | throw (IO.userError "private-cell plan missing")
  let _ ← checkPlan "private cell sevenfold" sevenfold [(7, 21), (0, 0), (high, high)]
  for (label, body, input, expected) in primitiveSteps do
    let plan ← checkedPlan label [.var 0] body 1
    let _ ← checkPlan label plan [(input, if input % 2 == 1 then expected else input)]
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations privateSource sevenfold
  IO.println (s!"aggregate loop source meaning: {fixedSteps.length} fixed steps " ++
    s!"under 4 masks, {primitiveSteps.length} raw primitive steps and {generated} generated " ++
    s!"plans agree with Core at their exact fuel; {loopFree} loop-free texts keep sourceCall")

end Tests.SourceLoopMeaning
