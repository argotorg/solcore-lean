import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ScalarMeaning.GenericEmitter
import Solcore.Test.SourceScalarMeaning

/-! Executable checks of the generic source meaning on actual generic emitter
output. Each emitted text is lexed, parsed with the generic grammar and run
under the generic source semantics, then compared with the original Core
reference on the Core machine. `Generic.emit_source_meaning` covers every
successful emission; these checks exercise the same definitions on real texts.
They also observe the final Core store, which the theorem leaves existential:
it holds the cells that the two step calls allocated. Loop-free texts keep
their `sourceCall` meaning, and altered selectors lose or change their
meaning. -/
set_option autoImplicit false

namespace Tests.SourceGenericMeaning

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.ScalarMeaning
open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The Word that Core returns and the number of cells in its final store,
each of which must be a Word. -/
private def coreRun (label : String) (program : Program) : IO (Nat × Nat) :=
  match program.runStateful 100000 with
  | .done (.word word) store => do
      ensure (store.all fun | .word _ => true | _ => false)
        s!"generic step allocated a cell that is not a Word: {label}"
      pure (word.val, store.length)
  | _ => throw (IO.userError s!"Core reference did not return a Word: {label}")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def call (index : Nat) (argument : Wire.Expr) : Wire.Expr := .apply (.var index) argument
private def entry : Wire.Expr := call 1 (.var 0)
private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def checkedPlan (label : String) (helpers : List Wire.Expr) (body : Wire.Expr)
    (variant : Variant) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
    throw (IO.userError s!"generic step failed the aggregate DAG checker: {label}")
  let some plan := CheckedPlan.ofParts? graph variant |
    throw (IO.userError s!"generic plan failed its checker: {label}")
  pure plan

private def emitted (label : String) (plan : CheckedPlan) : IO EmittedProgram :=
  match Generic.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generic emission failed: {label}: {reprStr error}")

/-- The emitted text parses with the generic grammar to a file whose printing is
that text, with the selector, one function per helper and `sc_step`, and the
aliases exactly when a step body uses one. The loop-free grammar rejects it. -/
private def checkReprint (label : String) (plan : CheckedPlan) (source : String) : IO Unit := do
  let some file := parseGenericSource source |
    throw (IO.userError s!"emitted generic source is outside the fragment: {label}")
  ensure (file.print == source) s!"parsed generic source does not print back: {label}"
  ensure (file.opcodeAliases == aggregateAliases (plan.step.helpers ++ [plan.step.entry]) &&
      (file.generics.map (·.name)) == ["sc_select"] &&
      file.functions.length == plan.step.helpers.length + 1 &&
      (file.functions.getLast?.map (·.name)) == some "sc_step" &&
      file.contract == Generic.contractName)
    s!"generic file has other aliases, functions or contract: {label}"
  ensure (parseSource source).isNone s!"the loop-free grammar accepted a generic text: {label}"

/-- Every boundary input and every input with a hand-known result agrees with
Core, and the final Core store has the expected number of cells. Returns the
emitted text. -/
private def checkPlan (label : String) (plan : CheckedPlan) (known : List (Nat × Nat) := [])
    (cells : Option Nat := none) : IO String := do
  let program ← emitted label plan
  checkReprint label plan program.source
  for input in known.map Prod.fst ++ Tests.SourceScalarMeaning.boundaryInputs do
    let (expected, stored) ← coreRun label (plan.instantiate (Word.ofNatModulo input)).toCore
    ensure (genericSourceCall program.source "run" [input] == some expected)
      s!"generic source meaning differs from Core: {label} at {input}"
    ensure (sourceCall program.source "run" [input] == none)
      s!"the loop-free meaning gave a generic text a result: {label} at {input}"
    if let some count := cells then
      ensure (stored == count) s!"generic Core store has another number of cells: {label}"
  for (input, expected) in known do
    ensure (genericSourceCall program.source "run" [input] == some expected)
      s!"generic source differs from its hand-known result: {label} at {input}"
  ensure (genericSourceCall program.source "run" [2 ^ 256] == none)
    s!"generic method accepted an argument outside uint256: {label}"
  return program.source

/-- The regression steps of `SourceGenericEmitter` at each variant, with their
hand-known results at the inputs 0, 1, the maximum Word and `2^255`. The
identity step allocates one cell per call, so its store ends with two. -/
private def identityWithCell : Wire.Expr := .letE (.newCell .word (.var 0)) (.loadCell (.var 0))

private def identityExpected : Variant → List Nat
  | .word => [1, 1, maximum, high + 1]
  | .pair => [2, 2, maximum - 1, 2]
  | .sum => [2, 1, maximum, high + 2]

private def incrementExpected : Variant → List Nat
  | .word => [2, 2, 0, high + 2]
  | .pair => [3, 3, maximum, 3]
  | .sum => [3, 2, 0, high + 3]

private def regressionChecks : IO String := do
  let inputs := [0, 1, maximum, high]
  let mut identitySource := ""
  for variant in Variant.all do
    let identity ← checkedPlan s!"identity {variant.name}" [identityWithCell] entry variant
    let source ← checkPlan s!"identity {variant.name}" identity
      (inputs.zip (identityExpected variant)) (some 2)
    if variant == .word then identitySource := source
    let increment ← checkedPlan s!"increment {variant.name}"
      [.binary .wordAdd (.var 0) (word 2)] (.binary .wordSub entry (word 1)) variant
    let _ ← checkPlan s!"increment {variant.name}" increment
      (inputs.zip (incrementExpected variant)) (some 0)
  let constant ← checkedPlan "constant" [word 42] entry .word
  let _ ← checkPlan "constant" constant (inputs.map fun input => (input, 42)) (some 0)
  return identitySource

/-- Raw opcodes applied to a helper result as the step, at each variant. -/
private def primitiveSteps : List (String × Wire.Expr) :=
  let c := call 1
  [("clz", .unary .wordClz (c (.var 0))),
    ("div", .binary .wordDiv (c (.var 0)) (c (word 2))),
    ("mod", .binary .wordMod (c (.var 0)) (c (word 0))),
    ("shl", .binary .wordShl (c (word 1)) (c (.var 0))),
    ("shr", .binary .wordShr (c (word maximum)) (c (.var 0))),
    ("sar", .binary .wordSar (c (word high)) (c (.var 0))),
    ("sdiv", .binary .wordSdiv (c (.var 0)) (c (word maximum))),
    ("smod", .binary .wordSmod (c (.var 0)) (c (word 2))),
    ("sgt", .ifE (.binary .wordSgt (c (.var 0)) (c (word 0))) (word 1) (word 0)),
    ("byte", .binary .wordByte (c (.var 0)) (c (word 0x1234))),
    ("pow", .binary .wordPow (c (word maximum)) (c (.var 0))),
    ("signextend", .binary .wordSignExtend (c (word 0)) (c (.var 0))),
    ("addmod", .ternary .wordAddMod (c (.var 0)) (c (word 1)) (c (word maximum))),
    ("mulmod", .ternary .wordMulMod (c (.var 0)) (c (word 2)) (c (word maximum)))]

/-- Plans from the `runtime-generics` generator at two budgets, which together
use every variant. Seeds the generator rejects are skipped. -/
private def checkGenerated : IO Nat := do
  let mut count := 0
  let mut variants : List Variant := []
  for nodes in [256, 512] do
    for seed in List.range 12 do
      match Generic.generatedPlan (Seed.ofNat seed) nodes with
      | .error _ => pure ()
      | .ok (plan, _) =>
          let _ ← checkPlan s!"generated budget {nodes} seed {seed}" plan
          variants := (variants ++ [plan.variant]).eraseDups
          count := count + 1
  ensure (count ≥ 16) s!"the generic generator produced only {count} plans"
  ensure (Variant.all.all variants.contains) "generated generic plans missed a variant"
  return count

/-- Loop-free aggregate texts keep their `sourceCall` meaning when read as
generic programs. -/
private def checkLoopFree : IO Nat := do
  let mut count := 0
  for (helpers, body) in [([identityWithCell], entry),
      ([.binary .wordAdd (.var 0) (word 1)],
        .caseE (.inRight .word (call 1 (.var 0))) (word 0) (.var 0))] do
    let some graph := Aggregates.CheckedDAG.ofParts? helpers body |
      throw (IO.userError "loop-free aggregate fixture failed its checker")
    let program ← match Aggregate.emit graph with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"aggregate emission failed: {reprStr error}")
    let some file := parseSource program.source |
      throw (IO.userError "emitted aggregate source is outside the loop-free fragment")
    ensure (file.toGeneric.print == program.source &&
        (parseGenericSource program.source).isSome)
      "the generic grammar changed a loop-free aggregate file"
    for input in Tests.SourceScalarMeaning.boundaryInputs ++ [2 ^ 256] do
      ensure (genericSourceCall program.source "run" [input] ==
          sourceCall program.source "run" [input])
        s!"generic meaning differs from sourceCall on a loop-free text at {input}"
    count := count + 1
  return count

/-- Altered selectors lose their meaning or change their result. -/
private def checkAlterations (source : String) : IO Unit := do
  let replace (old new : String) : IO String := do
    let changed := source.replace old new
    ensure (changed != source) s!"generic fixture has no {old}"
    pure changed
  let expected := genericSourceCall source "run" [1]
  let swapped ← replace "        return left;" "        return right;"
  ensure ((parseGenericSource swapped).isSome &&
      genericSourceCall swapped "run" [1] != expected)
    "a guard returning the other candidate kept its result"
  let unguarded ← replace "    if (flag) {\n        return left;\n    }\n" ""
  ensure ((parseGenericSource unguarded).isSome &&
      genericSourceCall unguarded "run" [1] != expected)
    "a selector without its guard kept its result"
  let wordFlag ← replace "flag: bool, left: a" "flag: word, left: a"
  ensure ((parseGenericSource wordFlag).isSome && genericSourceCall wordFlag "run" [1] == none)
    "a Boolean argument was admitted for a word parameter"
  let wordGuard ← replace "    if (flag) {" "    if (left) {"
  ensure ((parseGenericSource wordGuard).isSome && genericSourceCall wordGuard "run" [1] == none)
    "a guard on a word received a meaning"
  let twoOperators ← replace "sc_input + 1;" "sc_input + 1 + 1;"
  ensure (parseGenericSource twoOperators).isNone
    "two infix operations without parentheses were accepted"
  let stride ← replace "sc_input + 1;" "sc_input + 2;"
  ensure (genericSourceCall stride "run" [0] != genericSourceCall source "run" [0])
    "the right candidate ignored its input"

def testSourceGenericMeaning : IO Unit := do
  let identitySource ← regressionChecks
  let mut primitives := 0
  for (label, body) in primitiveSteps do
    for variant in Variant.all do
      let _ ← checkPlan s!"{label} {variant.name}" (← checkedPlan label [.var 0] body variant)
      primitives := primitives + 1
  let generated ← checkGenerated
  let loopFree ← checkLoopFree
  checkAlterations identitySource
  IO.println (s!"generic source meaning: 7 regression plans, {primitives} raw primitive " ++
    s!"plans and {generated} generated plans agree with Core; {loopFree} loop-free texts " ++
    "keep sourceCall")

end Tests.SourceGenericMeaning
