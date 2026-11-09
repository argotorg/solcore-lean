import Solcore.Synthesis.Internal.LanguageFeatures
import Solcore.Core.Machine
import Solcore.Synthesis.Internal.Functions
import Solcore.Core.Wire.Codec
import Solcore.Synthesis.Internal.Integers

/-!
# Scalar profile tests

The scalar runtime profiles: primitives, integers, inputs, functions, mutation, comptime, generics and
modules.
-/

section
-- leanmerge: from Solcore.Test.SourceComptimeCases
/-! Comptime cases retain original constant and runtime ASTs, execute both
independently, reject changed provenance, and shrink either typed component. -/
set_option autoImplicit false

namespace Tests.SourceComptimeCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Comptime (CheckedPlan Variant)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "comptime step fixture failed checked admission")
private def constant (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some value => pure value
  | none => throw (IO.userError "constant fixture is not a checked closed G0 Word")
private def constantBody : Wire.Expr :=
  .letE (.binary .wordAdd (word 2) (word 3))
    (.ifE (.binary .wordGt (.var 0) (word 4))
      (.binary .wordMul (.var 0) (word 2)) (word 0))
private def plan (fixed : CheckedWordProgram) (step : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? fixed step variant with
  | some value => pure value
  | none => throw (IO.userError "comptime plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Comptime.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- One private step cell is followed by the wrapper's mutable capture cell.
The entry differs from the last helper and must not be discarded by the wrapper. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.loadCell (.var 1)))

private def expected (variant : Variant) (input : Word) : Word :=
  if variant == .offset then input.add (Word.ofNatModulo 21)
  else (input.mul (Word.ofNatModulo 11)).add (Word.ofNatModulo 21)

private def referenceChecks : IO Unit := do
  let fixed ← constant constantBody
  ensure (Solcore.Synthesis.Source.observe fixed 10000 == returned (Word.ofNatModulo 10))
    "independent closed constant golden failed"
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for variant in [Variant.offset, .scale] do
    let value ← plan fixed graph variant
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes fixed.program + Wire.programNodes graph.program +
      Solcore.Synthesis.Core.Comptime.appliedOverhead variant)
      "comptime whole node budget omitted one original expression"
    let mut source : Option String := none
    for input in Comptime.boundaryInputs do
      ensure (Comptime.observe value input 10000 == returned (expected variant input))
        s!"comptime original-constant/entry mismatch: {variant.name}, input {input.val}"
      match (value.instantiate input).toCore.runStateful 10000 with
      | .done (.word _) store =>
          ensure (store == [.word (input.add (Word.ofNatModulo (if variant == .offset then 12 else 2)))])
            "comptime wrapper changed runtime step argument or called it more than once"
      | _ => throw (IO.userError "checked comptime reference did not return")
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "comptime source depends on runtime input"
      source := some current
      let admitted ← get (Comptime.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.variant == variant &&
        Wire.encodeProgram admitted.plan.constant.program == Wire.encodeProgram fixed.program)
        "comptime case lost one original checked expression"
      ensure ((← get (Comptime.replayCase saved 10000)) == saved) "imported comptime case did not replay"
      ensure ((← get (Comptime.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "comptime replay trusted its stored expected result"
      let low ← get (Comptime.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "comptime fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let literal ← constant (word 4)
  let literalPlan ← plan literal identity .offset
  ensure (!(Comptime.inputSensitive literalPlan 10000).isOk)
    "generated constant without an operation was admitted"
  ensure ((Comptime.emitCase literalPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
    "imported literal constant should remain supported"
  let constantStep ← checked [word 4]
  let constantPlan ← plan fixed constantStep .scale
  ensure (!(Comptime.inputSensitive constantPlan 10000).isOk)
    "generated comptime plan lost the step's input-sensitive requirement"
  let wrapped ← constant (.binary .wordAdd (.word Word.maximum) (word 1))
  for variant in [Variant.offset, .scale] do
    let wrappedPlan ← plan wrapped identity variant
    for input in Comptime.boundaryInputs do
      ensure (Comptime.observe wrappedPlan input 10000 == returned input)
        "original constant Word overflow was not preserved"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Comptime.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "comptime skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/variant residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default comptime budget cannot hold a selected template skeleton"
    let (value, _) ← get (Comptime.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.variant == Comptime.variantFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "comptime generation escaped its full node, variant or helper constraints"
    ensure (!(Comptime.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Comptime.generatedPlan (Seed.ofNat seed) 513).isOk) "comptime node bounds were not enforced"
  let corpus := Comptime.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Comptime.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "comptime generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded comptime generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Comptime.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Comptime.boundaryInputs[index % 4]?) "comptime generation changed boundary order/budget"
    ensure ((← get (Comptime.replayCase row 10000)) == row) "generated comptime provenance did not replay"
    let low ← get (Comptime.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh comptime observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Comptime.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "comptime generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Comptime.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Comptime.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "comptime count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Comptime.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Comptime.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty comptime generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Comptime.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered comptime version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("variant", toJson "forged"),
      ("stepOrigin", Json.null), ("constantOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered comptime {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let constantOrigin ← field origin "constantOrigin"
  for name in ["kind", "seed", "finalSeed", "maxProgramNodes"] do
    rejected (Comptime.replayCase (withOrigin (origin.setObjVal! "constantOrigin"
      (constantOrigin.setObjVal! name Json.null))) 10000) "tampered constant recipe accepted"
  rejected (Comptime.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "constantFeatures" (toJson ([] : List String)))) 10000)
    "tampered constant feature provenance accepted"
  let admitted ← get (Comptime.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "comptime-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Comptime.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Comptime.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let comptimePlan ← field saved "comptimePlan"
  let changedConstant ← constant (word 17)
  rejected (Comptime.caseProgram (saved.setObjVal! "comptimePlan"
    (comptimePlan.setObjVal! "constantProgram" (Wire.encodeProgram changedConstant.program))))
    "changed constant program was not compared against the full original reference"
  let free : Wire.Program := {resultType := .word, dataDefinitions := [], body := .var 0}
  rejected (Comptime.checkedPlan (comptimePlan.setObjVal! "constantProgram" (Wire.encodeProgram free)))
    "constant captured an outer runtime input"
  for (name, value) in [("variant", toJson "unknown"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Comptime.checkedPlan (comptimePlan.setObjVal! name value)) "malformed comptime plan accepted"
  rejected (Comptime.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical comptime input accepted"
  rejected (Comptime.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Comptime.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale comptime source accepted"
  let contract ← field saved "contract"
  rejected (Comptime.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong comptime ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let fixed ← constant constantBody
  let value ← plan fixed graph .scale
  let saved ← imported value Word.maximum
  let original ← get (Comptime.caseProgram saved)
  let shrunk ← get (Comptime.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Comptime.shrinkCases saved 1000 10000)))
    "comptime shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  let mut constantReduced := false
  for row in rows do
    let candidate ← get (Comptime.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.variant == value.variant)
      "comptime reduction lost a step binder/helper or changed its comptime variant"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "comptime reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "comptime reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Comptime.replayCase row 10000)) == row) "comptime reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    constantReduced := constantReduced || Wire.encodeProgram candidate.plan.constant.program != Wire.encodeProgram fixed.program
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced && constantReduced) "comptime reduction omitted constant, input or step candidates"
  ensure ((← cases (← get (Comptime.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Comptime.shrinkCases saved 0 10000))).isEmpty) "comptime shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Comptime.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Comptime.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Comptime.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Comptime.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceComptimeCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceComptimeCases
end

section
-- leanmerge: from Solcore.Test.SourceComptimeEmitter
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
  ensure (Solcore.Synthesis.Source.Comptime.emitterVersion == "solcore-source-comptime-v3" &&
    Solcore.Synthesis.Source.Comptime.wrapperVersion == "solcore-word-comptime-contract-v1" &&
    Solcore.Synthesis.Source.Comptime.selector == "0xa444f5e9" &&
    Comptime.version == "core-comptime-word-plan-v1") "comptime provenance changed"

def testSourceComptimeEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceComptimeEmitter
end

section
-- leanmerge: from Solcore.Test.SourceFunctionCases
/-! Bounded acyclic-function generation, original Core execution, provenance
replay and checked shrinking. This does not assume source-printer correctness. -/
set_option autoImplicit false

namespace Tests.SourceFunctionCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejected {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def checked (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "function case fixture did not typecheck")

private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def diamond : List Wire.Expr := [
  .binary .wordXor (.var 0) (word 3),
  .letE (.apply (.var 1) (.var 0)) (.binary .wordAdd (.var 0) (.var 1)),
  .binary .wordXor (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 0))]

private def imported (helpers : List Wire.Expr) (input : Word) : IO Json := do
  get (Function.emitCase (← checked helpers entry) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def originalCoreChecks : IO Unit := do
  let graph ← checked diamond entry
  ensure (graph.features.count "functionCall" == 4) "callee variables were mistaken for scalar expressions"
  let mut emitted : Option String := none
  for input in Input.boundaryInputs do
    let saved ← get (Function.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let zero := Word.ofNatModulo 3
    let first := input.bitXor zero
    let expected := (first.add input).bitXor first
    ensure ((← field saved "directCore") == returned expected) "diamond calls changed original Core meaning"
    let source ← string saved "source"
    if let some previous := emitted then ensure (previous == source) "source text depends on the input"
    emitted := some source
    let admitted ← get (Function.caseProgram saved)
    ensure (admitted.program.check && admitted.function.helpers.length == 3)
      "applied diamond escaped full checker/shape admission"
    ensure ((← get (Function.replayCase saved 1000)) == saved) "imported DAG did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 777))
    ensure ((← get (Function.replayCase forged 1000)) == saved) "stored expected result was trusted"
    let low ← get (Function.replayCase saved 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "original Core fuel exhaustion was treated as a value"
  let constant ← checked [word 17] (word 3)
  let saved ← get (Function.emitCase constant Word.maximum
    (Json.mkObj [("kind", toJson "imported")]) 1000)
  ensure ((← field saved "directCore") == returned (Word.ofNatModulo 3))
    "constant reduced/imported DAG must remain admissible"
  rejected (Function.inputSensitive constant 1000) "constant generated graph passed the input filter"
  let unsupported ← checked [.binary .wordDiv (.var 0) (word 2)] entry
  rejected (Function.emitCase unsupported Word.zero (Json.mkObj [("kind", toJson "imported")]) 1000)
    "unsupported scalar operation silently entered the function emitter"
  let large := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  let oversized ← checked [large] entry
  rejected (Function.emitCase oversized Word.zero (Json.mkObj [("kind", toJson "imported")]) 1000)
    "oversized applied DAG escaped the 512-node case limit"

private def generationChecks : IO Json := do
  let mut last := Json.null
  for seed in List.range 3 do
    let count := seed + 1
    let budget := 9 * count + 6
    let corpus := Function.generateCases (Seed.ofNat seed) budget 4 1 1000
    ensure (corpus == Function.generateCases (Seed.ofNat seed) budget 4 1 1000)
      "helper generation is not deterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimum valid helper budget did not emit its fixed function"
    let rows ← cases corpus
    ensure (rows.size == 4) "one function did not emit its four boundary cases"
    for index in List.range 4 do
      let saved := rows[index]!
      let admitted ← get (Function.caseProgram saved)
      ensure (admitted.function.helpers.length == count && admitted.program.check &&
        Wire.programNodes admitted.program ≤ budget) "generation violated helper count/type/node budget"
      ensure (some admitted.input == Input.boundaryInputs[index]?) "boundary ordering changed"
      ensure ((← field saved "directCore") == returned (admitted.input.mul (Word.ofNatModulo count)))
        "generated entry did not execute its complete helper chain"
      ensure ((← get (Function.replayCase saved 1000)) == saved) "generated DAG replay differs"
      let low ← get (Function.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "replay failed to separate validation fuel from fresh observation fuel"
      last := saved
    let tooSmall := Function.generateCases (Seed.ofNat seed) (budget - 1) 1 1 1000
    ensure ((← cases tooSmall).isEmpty && (← string tooSmall "status") == "generation-exhausted")
      "small budget silently changed the helper count"
  let varied := Function.generateCases (Seed.ofNat 0) 48 12 256 1000
  ensure ((← cases varied).size == 12 && (← natural varied "attempted") ≤ 256)
    "bounded mixed helper generation failed"
  for saved in ← cases varied do
    let admitted ← get (Function.caseProgram saved)
    ensure (Wire.programNodes admitted.program ≤ 48) "mixed helper generation exceeded requested budget"
    ensure ((← get (Function.replayCase saved 1000)) == saved) "mixed helper provenance did not replay"
  let low := Function.generateCases (Seed.ofNat 0) 15 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource" &&
    (← string excluded[0]! "code") == "boundary-out-of-fuel") "generation fuel was a semantic exclusion"
  ensure ((← cases (Function.generateCases (Seed.ofNat 0) 15 3 1 1000)).size == 3)
    "count did not truncate the final boundary group"
  ensure ((← string (Function.generateCases (Seed.ofNat 0) 15 5 1 1000) "status") == "generation-exhausted")
    "function attempts were confused with input case count"
  ensure ((← natural (Function.generateCases (Seed.ofNat 0) 48 0 100 1000) "attempted") == 0)
    "zero case count consumed generation attempts"
  ensure ((← cases (Function.generateCases (Seed.ofNat 0) 48 1 0 1000)).isEmpty)
    "zero attempt budget was ignored"
  let wrapped := Function.generateCases (Seed.ofNat (2 ^ 64 - 2)) 33 4 1 1000
  for saved in ← cases wrapped do
    ensure ((← get (Function.replayCase saved 1000)) == saved) "uint64 helper seed wrap did not replay"
  ensure ((← cases wrapped).size == 4) "uint64 seed-wrap fixture did not emit"
  return last

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun replacement => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" replacement)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "abstractionVersion",
      "emitterVersion", "wrapperVersion"] do
    rejected (Function.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helperCount", toJson (0 : Nat)),
      ("inputIndex", toJson (999 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("helpers", Json.arr #[]), ("kind", toJson "unknown")] do
    rejected (Function.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} provenance accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  let first := metadata[0]!
  for (name, value) in [("seed", toJson "0"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (99 : Nat)), ("maxProgramNodes", toJson (99 : Nat))] do
    rejected (Function.replayCase (withOrigin (origin.setObjVal! "helpers"
      (.arr (metadata.set! 0 (first.setObjVal! name value))))) 1000) "tampered helper provenance accepted"
  rejected (Function.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000) "stale source accepted"
  rejected (Function.replayCase (saved.setObjVal! "input" (toJson "0")) 1000) "input/program mismatch accepted"
  let contract ← field saved "contract"
  rejected (Function.replayCase (saved.setObjVal! "contract"
    (contract.setObjVal! "calldata" (toJson "0xa444f5e9"))) 1000) "incorrect ABI argument accepted"
  rejected (Function.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ["functionCall"]))) 1000) "incorrect features accepted"
  for helpers in [[], [.apply (.var 1) (.var 0)], [.var 0, .apply (.var 2) (.var 0)],
      [.var 0, .var 0, .var 0, .var 0]] do
    rejected (Function.checkedFunction (Wire.encodeProgram (functionDAGProgram helpers entry)))
      "empty/recursive/forward-reference/too-many-helper DAG accepted"
  let (constant, constantOrigin) ← get (Function.generatedFunction (Seed.ofNat 83) 48)
  let forgedOrigin := (constantOrigin.setObjVal! "inputIndex" (toJson (0 : Nat))).setObjVal!
    "validationFuel" (toJson (1000 : Nat))
  let forged ← get (Function.emitCase constant Word.zero forgedOrigin 1000)
  rejected (Function.replayCase forged 1000)
    "constant-on-boundaries generated graph escaped sensitivity revalidation"

private def shrinkChecks : IO Unit := do
  let saved ← imported diamond Word.maximum
  let original ← get (Function.caseProgram saved)
  let shrunk ← get (Function.shrinkCases saved 1000 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Function.shrinkCases saved 1000 1000)))
    "function shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut bodyReduced := false
  for row in rows do
    let candidate ← get (Function.caseProgram row)
    ensure (candidate.program.check && candidate.function.helpers.length == original.function.helpers.length &&
      Wire.programNodes candidate.program ≤ 512) "shrink changed helper count or broke checker/shape"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "function shrink did not strictly reduce applied Core complexity"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "function shrink duplicated a candidate"
    seen := key :: seen
    ensure ((← get (Function.replayCase row 1000)) == row) "function shrink failed replay"
    let emitted ← get ((Function.emit candidate.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "function shrink retained stale source"
    inputReduced := inputReduced || candidate.input != original.input
    bodyReduced := bodyReduced || Wire.encodeProgram candidate.function.program !=
      Wire.encodeProgram original.function.program
  ensure (inputReduced && bodyReduced) "function shrink omitted body/input reductions"
  ensure ((← cases (← get (Function.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "function shrink limit changed ordering"
  ensure ((← cases (← get (Function.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Function.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 10 1000)
    "function shrink accepted stale source"

def testSourceFunctionCases : IO Unit := do
  originalCoreChecks
  let generated ← generationChecks
  tamperingChecks generated
  shrinkChecks

end Tests.SourceFunctionCases
end

section
-- leanmerge: from Solcore.Test.SourceFunctionEmitter
/-! Named-function source regressions. The original Core graphs independently
exercise ordered declarations, diamond dependencies and calls under local
binders. Printer tests do not establish compiler meaning preservation. -/
set_option autoImplicit false

namespace Tests.SourceFunctionEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

def entry : Wire.Expr := .apply (.var 1) (.var 0)

def singleHelpers : List Wire.Expr := [.binary .wordAdd (.var 0) (word 1)]

def chainHelpers : List Wire.Expr := singleHelpers ++ [
  .binary .wordMul (.var 0) (.apply (.var 1) (.var 0))]

/-- The last helper calls both earlier helpers. Its inner binder shifts the
callee index, while the parameter must remain distinct from the new local. -/
def diamondHelpers : List Wire.Expr := singleHelpers ++ [
  .binary .wordAdd (.var 0) (.apply (.var 1) (.var 0)),
  .letE (.apply (.var 2) (.var 0))
    (.binary .wordSub (.apply (.var 2) (.var 1)) (.var 0))]

def scopedHelpers : List Wire.Expr := singleHelpers ++ [
  .letE (word 7) (.ifE (.binary .wordGt (.var 1) (word 0))
    (.letE (word 11) (.apply (.var 3) (.binary .wordAdd (.var 0) (.var 2))))
    (.letE (word 22) (.apply (.var 3) (.binary .wordSub (.var 2) (.var 1)))))]

def fixtures : List (String × List Wire.Expr × Wire.Expr) := [
  ("single", singleHelpers, entry), ("chain", chainHelpers, entry),
  ("diamond", diamondHelpers, entry), ("branch-locals", scopedHelpers, entry)]

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "function graph fixture failed checked profile admission")

private def emitted (graph : CheckedWordFunctionDAG) : IO EmittedProgram :=
  match Function.emit graph with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"function graph emission failed: {reprStr error}")

private def observe (graph : CheckedWordFunctionDAG) (input expected : Nat) : IO Unit := do
  let applied := graph.instantiate (Word.ofNatModulo input)
  ensure applied.check "original applied function graph failed Core typing"
  match applied.toCore.runStateful 2000 with
  | .done (.word actual) _ => ensure (actual.val == expected) "original Core function graph result changed"
  | _ => throw (IO.userError "original Core function graph did not return a Word")

private def admissionChecks : IO Unit := do
  for (label, helpers, body) in fixtures do
    let graph ← checked helpers body
    ensure (graph.program.check && functionHelpersAccepted helpers &&
      functionAcceptsAt 1 helpers.length .word body) s!"graph was not fully admitted: {label}"
    let some restored := CheckedWordFunctionDAG.ofProgram? graph.program |
      throw (IO.userError s!"canonical graph failed readmission: {label}")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram graph.program)
      s!"graph readmission reordered declarations: {label}"
    let source ← emitted graph
    ensure (source == (← emitted graph)) s!"graph emission was not deterministic: {label}"
    ensure (source.contractName == "SynthesizedFunctions" && source.methodSignature == "run(uint256)" &&
      source.deployPath == ["SynthesizedFunctionsDeploy"] &&
      source.runtimePath == ["SynthesizedFunctionsDeploy", "SynthesizedFunctions"])
      s!"graph wrapper metadata changed: {label}"
  ensure (CheckedWordFunctionDAG.ofParts? [] (.var 0)).isNone "empty helper graph was admitted"
  ensure (CheckedWordFunctionDAG.ofParts? (List.replicate 4 (.var 0)) entry).isNone
    "helper count exceeded the fixed profile bound"
  for helpers in [
      [(.apply (.var 1) (.var 0) : Wire.Expr)],
      singleHelpers ++ [.apply (.var 2) (.var 0)],
      [(.var 1 : Wire.Expr)],
      [(.apply (.var 0) (.var 0) : Wire.Expr)],
      [(.letE (.lambda .word .word (.var 0)) (.apply (.var 0) (word 1)) : Wire.Expr)]] do
    ensure (CheckedWordFunctionDAG.ofParts? helpers entry).isNone
      "graph admitted a recursive/forward/escaping/local function or host reference"
  -- The Core host context really contains Word-to-Word functions. The scalar
  -- profile, not a coincidental type error, must reject these out-of-graph calls.
  let hostRead := functionDAGProgram [.apply (.var 1) (.var 0)] entry
  ensure hostRead.check "host-reference boundary fixture stopped exercising a well-typed Core program"
  ensure (CheckedWordFunctionDAG.ofProgram? hostRead).isNone
    "full Core typing bypassed the graph's closed scope boundary"
  for body in [
      (.apply (.var 2) (.var 0) : Wire.Expr),
      .apply (.ifE (.bool true) (.var 1) (.var 1)) (.var 0),
      .var 1, .bool false, .lambda .word .word (.var 0)] do
    ensure (CheckedWordFunctionDAG.ofParts? singleHelpers body).isNone
      "graph entry admitted an out-of-profile function expression"
  let single ← checked singleHelpers
  for program in [
      {single.program with dataDefinitions := [{constructorPayloadTypes := []}]},
      {single.program with resultType := .word},
      {single.program with body := .lambda .word .word (.var 0)},
      {single.program with body := .letE (word 1) (.lambda .word .word (.var 0))}] do
    ensure (CheckedWordFunctionDAG.ofProgram? program).isNone
      "graph decoder accepted a different declaration shape"

private def executionChecks : IO Unit := do
  let single ← checked singleHelpers
  let chain ← checked chainHelpers
  let diamond ← checked diamondHelpers
  let withLocals ← checked scopedHelpers
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do
    observe single input ((Word.ofNatModulo (input + 1)).val)
    observe diamond input input
  for (input, result) in [(0, 0), (1, 2), (Word.maximum.val, 0), (2 ^ 255, 2 ^ 255)] do
    observe chain input result
  for (input, result) in [(0, Word.maximum.val - 5), (1, 13),
      (Word.maximum.val, 11), (2 ^ 255, 2 ^ 255 + 12)] do
    observe withLocals input result
  match (chain.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel graph execution was treated as complete")
  for (body, expected) in [
      (.unary .wordClz (.var 0), EmitError.unsupportedUnary .wordClz),
      (.binary .wordDiv (.var 0) (word 0), .unsupportedBinary .wordDiv),
      (.ternary .wordMulMod (.var 0) (word 1) (word 2), .unsupportedTernary .wordMulMod)] do
    -- Even an unused helper must not be silently dropped by source emission.
    match Function.emit (← checked [body] (word 0)) with
    | .error actual => ensure (actual == expected) "unsupported graph operation returned the wrong error"
    | .ok _ => throw (IO.userError "unsupported graph operation was silently emitted")

private def chainExpected : String := String.intercalate "\n" [
  "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_fn1(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);",
  "    let sc_v1: word = (sc_arg * sc_v0);", "    return sc_v1;", "}", "",
  "contract SynthesizedFunctions {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_v0: word = sc_fn1(sc_input);",
  "        return uint256(sc_v0);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  ensure ((← emitted (← checked chainHelpers)).source == chainExpected)
    "helper declaration order, runtime parameter or direct-call rendering changed"
  let diamond ← checked diamondHelpers
  let source ← emitted diamond
  let third := String.intercalate "\n" [
    "function sc_fn2(sc_arg: word) returns (word) {",
    "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = sc_v0;",
    "    let sc_v2: word = sc_fn1(sc_arg);", "    let sc_v3: word = (sc_v2 - sc_v1);",
    "    return sc_v3;", "}"]
  ensure ((source.source.splitOn third).length == 2)
    "inner local shifted a helper reference to the wrong declaration"
  let scopedSource ← emitted (← checked scopedHelpers)
  let beforeCall := String.intercalate "\n" [
    "        let sc_v7: word = (sc_v6 + sc_arg);",
    "        let sc_v8: word = sc_fn0(sc_v7);"]
  ensure ((scopedSource.source.splitOn beforeCall).length == 2)
    "branch-local argument computation escaped its block or moved after its call"
  let single ← checked singleHelpers
  ensure (single.features == ["binary:Solcore.Core.Wire.BinaryOp.wordAdd", "local", "wordLiteral",
    "functionCall", "local"]) "function features counted declaration wrappers or callee locals"
  ensure ((diamond.features.filter (· == "functionCall")).length == 4)
    "diamond feature inventory lost a helper dependency"
  ensure (Function.emitterVersion == "solcore-source-functions-v2" &&
    Function.wrapperVersion == "solcore-word-functions-contract-v1" &&
    Function.selector == "0xa444f5e9" && wordFunctionDAGVersion == "core-word-function-dag-v1")
    "named-function provenance changed"

def testSourceFunctionEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceFunctionEmitter
end

section
-- leanmerge: from Solcore.Test.SourceGenericCases
/-! Generic-case regressions check eager evaluation order, selected payload
consumption, canonical references, provenance and sealed scope-preserving reductions. -/
set_option autoImplicit false

namespace Tests.SourceGenericCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "generic step fixture failed checked admission")
private def plan (step : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? step variant with
  | some value => pure value
  | none => throw (IO.userError "generic plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Generic.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- Final cell contents distinguish left/right input and expose call order.
The entry differs from the last helper and must not be discarded by the wrapper. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.loadCell (.var 1)))

private def expected (variant : Variant) (input : Word) : Word :=
  let odd := input.bitAnd (Word.ofNatModulo 1) == Word.ofNatModulo 1
  let selected := input.add (Word.ofNatModulo (if odd then 1 else 2))
  match variant with
  | .word => selected
  | .pair => selected.add (if odd then input else input.add (Word.ofNatModulo 1))
  | .sum => if odd then selected else selected.add (Word.ofNatModulo 1)

private def referenceChecks : IO Unit := do
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  for variant in [Variant.word, .pair, .sum] do
    let value ← plan graph variant
    ensure (Wire.programNodes (value.instantiate Word.zero) ==
      Wire.programNodes graph.program + Solcore.Synthesis.Core.Generic.appliedOverhead variant)
      "measured generic overhead differs from the complete original reference"
    let mut source : Option String := none
    for input in Generic.boundaryInputs do
      ensure (Generic.observe value input 10000 == returned (expected variant input))
        s!"generic selection/payload/entry mismatch: {variant.name}, input {input.val}"
      match (value.instantiate input).toCore.runStateful 10000 with
      | .done (.word _) store =>
          ensure (store.length == 2) "generic arguments were not both evaluated eagerly"
          ensure (store == [.word (input.add (Word.ofNatModulo 2)),
            .word (input.add (Word.ofNatModulo 3))]) "generic arguments changed order or reused a private cell"
      | _ => throw (IO.userError "checked generic reference did not return")
      let saved ← imported value input
      let current ← string saved "source"
      if let some previous := source then ensure (current == previous) "generic source depends on runtime input"
      source := some current
      let admitted ← get (Generic.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input && admitted.plan.variant == variant)
        "generic case lost its checked canonical reference"
      ensure ((← get (Generic.replayCase saved 10000)) == saved) "imported generic case did not replay"
      ensure ((← get (Generic.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
        "generic replay trusted its stored expected result"
      let low ← get (Generic.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "generic fuel exhaustion was treated as completion"
  let constant ← checked [word 4]
  for variant in [Variant.word, .pair, .sum] do
    let constantPlan ← plan constant variant
    ensure (!(Generic.inputSensitive constantPlan 10000).isOk)
      "generated generic plan lost the step's input-sensitive requirement"
    ensure ((Generic.emitCase constantPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
      "imported constant step should remain supported"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Generic.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "generic skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template/variant residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 384) "default generic budget cannot hold a selected template skeleton"
    let (value, _) ← get (Generic.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.variant == Generic.variantFor (Seed.ofNat seed) && value.step.helpers.length == 1 + seed % 3)
      "generic generation escaped its full node, variant or helper constraints"
    ensure (!(Generic.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Generic.generatedPlan (Seed.ofNat seed) 513).isOk) "generic node bounds were not enforced"
  let corpus := Generic.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Generic.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "generic generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded generic generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Generic.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Generic.boundaryInputs[index % 4]?) "generic generation changed boundary order/budget"
    ensure ((← get (Generic.replayCase row 10000)) == row) "generated generic provenance did not replay"
    let low ← get (Generic.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh generic observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Generic.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "generic generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Generic.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Generic.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "generic count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Generic.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Generic.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty generic generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Generic.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered generic version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)), ("variant", toJson "forged"),
      ("stepOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Generic.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered generic {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Generic.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let admitted ← get (Generic.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "generic-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Generic.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Generic.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let genericPlan ← field saved "genericPlan"
  for (name, value) in [("variant", toJson "unknown"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Generic.checkedPlan (genericPlan.setObjVal! name value)) "malformed generic plan accepted"
  rejected (Generic.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical generic input accepted"
  rejected (Generic.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Generic.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale generic source accepted"
  let contract ← field saved "contract"
  rejected (Generic.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong generic ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let value ← plan graph .sum
  let saved ← imported value Word.maximum
  let original ← get (Generic.caseProgram saved)
  let shrunk ← get (Generic.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Generic.shrinkCases saved 1000 10000)))
    "generic shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  for row in rows do
    let candidate ← get (Generic.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph &&
      candidate.plan.variant == value.variant)
      "generic reduction lost a step binder/helper or changed its generic variant"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "generic reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "generic reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Generic.replayCase row 10000)) == row) "generic reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced) "generic reduction omitted input or step candidates"
  ensure ((← cases (← get (Generic.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Generic.shrinkCases saved 0 10000))).isEmpty) "generic shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Generic.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Generic.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Generic.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Generic.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceGenericCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceGenericCases
end

section
-- leanmerge: from Solcore.Test.SourceGenericEmitter
/-! Monomorphic Core selection and a polymorphic source definition. Explicit
boundary goldens cover both selector branches, aggregate payloads and wrapping
addition. Private cell traces establish eager left-to-right candidate evaluation. -/
set_option autoImplicit false

namespace Tests.SourceGenericEmitter

open Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.Generic (CheckedPlan Variant)
open Solcore.Synthesis.Source (EmittedProgram)

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def identityWithCell : Wire.Expr :=
  .letE (.newCell .word (.var 0)) (.loadCell (.var 0))
private def incrementTwo : Wire.Expr := .binary .wordAdd (.var 0) (word 2)
private def arbitraryEntry : Wire.Expr := .binary .wordSub entry (word 1)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def step (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "generic step did not pass the aggregate checker")

private def checked (graph : Aggregates.CheckedDAG) (variant : Variant) : IO CheckedPlan :=
  match CheckedPlan.ofParts? graph variant with
  | some plan => pure plan
  | none => throw (IO.userError "generic monomorphic wrapper failed full Core admission")

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.Generic.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"generic source emission failed: {reprStr error}")

private def inputs : List Nat := [0, 1, Word.maximum.val, 2 ^ 255]

private def identityExpected : Variant → List Nat
  | .word => [1, 1, Word.maximum.val, 2 ^ 255 + 1]
  | .pair => [2, 2, Word.maximum.val - 1, 2]
  | .sum => [2, 1, Word.maximum.val, 2 ^ 255 + 2]

private def incrementExpected : Variant → List Nat
  | .word => [2, 2, 0, 2 ^ 255 + 2]
  | .pair => [3, 3, Word.maximum.val, 3]
  | .sum => [3, 2, 0, 2 ^ 255 + 3]

private def observe (plan : CheckedPlan) (input expected : Nat) (cells : List Word) : IO Unit := do
  let applied := plan.instantiate (Word.ofNatModulo input)
  ensure applied.check "applied generic plan failed full Core checking"
  match applied.toCore.runStateful 10000 with
  | .done (.word value) store =>
      ensure (value.val == expected)
        s!"generic result changed: {plan.variant.name}, input {input}, expected {expected}, got {value.val}"
      ensure (store == cells.map Value.word)
        "generic candidate evaluation was lazy, reordered or shared a private cell"
  | _ => throw (IO.userError "generic Core application did not return a Word")

private def executionChecks : IO Unit := do
  let identity ← step [identityWithCell]
  let arbitrary ← step [incrementTwo] arbitraryEntry
  for variant in Variant.all do
    let identityPlan ← checked identity variant
    let arbitraryPlan ← checked arbitrary variant
    for (input, expected) in inputs.zip (identityExpected variant) do
      observe identityPlan input expected
        [Word.ofNatModulo input, Word.ofNatModulo (input + 1)]
    for (input, expected) in inputs.zip (incrementExpected variant) do
      observe arbitraryPlan input expected []
    match (identityPlan.instantiate Word.zero).toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was mistaken for generic completion")
  let constant ← checked (← step [word 42]) .word
  for input in inputs do observe constant input 42 []

private def admissionChecks : IO Unit := do
  for (variant, overhead) in Variant.all.zip [55, 79, 80] do
    ensure (Variant.ofString? variant.name == some variant) "generic variant is not canonical"
    for graph in [← step [identityWithCell], ← step [incrementTwo] arbitraryEntry] do
      let plan ← checked graph variant
      ensure (plan.program.check && plan.variant == variant &&
        plan.program.resultType == .function .word .word)
        "generic plan changed variant or escaped whole-program checking"
      match plan.program.body with
      | .letE saved (.letE (.lambda .bool _ _) (.lambda .word .word _)) =>
          ensure (Wire.encodeExpr saved == Wire.encodeExpr graph.program.body)
            "generic wrapper ignored its arbitrary checked step entry"
      | _ => throw (IO.userError "generic wrapper lost its explicit monomorphic selector closure")
      let measured := Wire.programNodes (plan.instantiate Word.maximum)
      ensure (measured == Generic.appliedNodes graph variant &&
        measured == Generic.canonicalNodes graph variant &&
        measured == Wire.programNodes graph.program + Generic.appliedOverhead variant &&
        Generic.appliedOverhead variant == overhead)
        "generic node overhead differs from the complete original Core application"
      ensure ((← emitted plan) == (← emitted plan)) "generic source emission is nondeterministic"
  for invalid in ["", "Word", "tuple", "sum<word,word>", "word "] do
    ensure (Variant.ofString? invalid).isNone "generic variant parsing accepted noncanonical metadata"
  -- Raw primitives render through the call-graph helpers with the alias import.
  let divided ← step [.binary .wordDiv (.var 0) (word 1)]
  for variant in Variant.all do
    match Solcore.Synthesis.Source.Generic.emit (← checked divided variant) with
    | .ok emitted =>
        unless (emitted.source.splitOn "import { div as sc_div, mod as sc_mod, ").length == 2 &&
            (emitted.source.splitOn "    let sc_v3: word = sc_div(sc_v0, sc_v2);").length == 2 do
          throw (IO.userError "generic emission lost the raw division alias or its operand snapshots")
    | .error error => throw (IO.userError s!"generic raw division was rejected: {reprStr error}")

private def contains (source fragment : String) : Bool := (source.splitOn fragment).length > 1

private def formattingChecks : IO Unit := do
  let graph ← step [incrementTwo] arbitraryEntry
  let definition := String.intercalate "\n" [
    "function sc_select<a>(flag: bool, left: a, right: a) returns (a) {",
    "    if (flag) {", "        return left;", "    }", "    return right;", "}"]
  let eager := String.intercalate "\n" [
    "        let sc_left_word: word = sc_step(sc_input);",
    "        let sc_next: word = sc_input + 1;",
    "        let sc_right_word: word = sc_step(sc_next);",
    "        let sc_flag: bool = ((sc_input & 1) == 1);"]
  for variant in Variant.all do
    let source ← emitted (← checked graph variant)
    ensure (contains source.source definition && contains source.source eager &&
      (source.source.splitOn "function sc_select<").length == 2 &&
      (source.source.splitOn " = sc_select(").length == 2)
      "generic source lost its polymorphic definition or eager ordered candidate calls"
    ensure (contains source.source (String.intercalate "\n" [
      "function sc_step(sc_arg: word) returns (word) {",
      "    let sc_v0: word = sc_fn0(sc_arg);", "    let sc_v1: word = 1;",
      "    let sc_v2: word = (sc_v0 - sc_v1);", "    return sc_v2;", "}"]))
      "generic source replaced the arbitrary entry with its last helper"
    ensure (source.contractName == "SynthesizedGenerics" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedGenericsDeploy"] &&
      source.runtimePath == ["SynthesizedGenericsDeploy", "SynthesizedGenerics"])
      "generic wrapper metadata changed"
    match variant with
    | .word =>
        ensure (contains source.source "let sc_selected: word = sc_select(")
          "Word generic instantiation disappeared"
    | .pair =>
        ensure (contains source.source "let sc_selected: (word, word) = sc_select(" &&
          contains source.source "sc_result = sc_first + sc_second;")
          "product generic instantiation lost its fields"
    | .sum =>
        ensure (contains source.source "let sc_selected: sum<word, word> = sc_select(" &&
          contains source.source "case inl(sc_payload)" && contains source.source "case inr(sc_payload)" &&
          contains source.source "sc_result = sc_payload + 1;")
          "sum generic instantiation lost its constructor-dependent result"
  ensure (Solcore.Synthesis.Source.Generic.emitterVersion == "solcore-source-generics-v3" &&
    Solcore.Synthesis.Source.Generic.wrapperVersion == "solcore-word-generics-contract-v1" &&
    Solcore.Synthesis.Source.Generic.selector == "0xa444f5e9" &&
    Generic.version == "core-generic-selection-plan-v1") "generic provenance changed"

def testSourceGenericEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceGenericEmitter
end

section
-- leanmerge: from Solcore.Test.SourceInputCases
/-! Runtime-input generation, original-Core observation, strict replay and
closed-lambda shrinking. Compiler agreement is checked separately by the real
Rust/Core/EVM integration runner. -/
set_option autoImplicit false

namespace Tests.SourceInputCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejected {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def function (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some checked => pure checked
  | none => throw (IO.userError "input-case fixture did not typecheck")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def field (value : Json) (key : String) : IO Json := get (value.getObjVal? key)
private def string (value : Json) (key : String) : IO String := get (value.getObjValAs? String key)
private def natural (value : Json) (key : String) : IO Nat := get (value.getObjValAs? Nat key)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")

private def imported (body : Wire.Expr) (input : Word) : IO Json := do
  get (Input.emitCase (← function body) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def inputChecks : IO Unit := do
  for input in Input.boundaryInputs do
    ensure ((← get (Input.inputWord (toString input.val))) == input) "boundary input round trip failed"
    let encoded := Input.calldata input
    ensure (encoded.length == 74 && encoded.startsWith Input.selector) "ABI input width/selector changed"
  ensure (Input.calldata Word.zero == "0xa444f5e9" ++ String.ofList (List.replicate 64 '0'))
    "zero input ABI encoding changed"
  ensure (Input.calldata Word.maximum == "0xa444f5e9" ++ String.ofList (List.replicate 64 'f'))
    "maximum input ABI encoding changed"
  ensure (Input.calldata (Word.ofNatModulo (2 ^ 255)) ==
    "0xa444f5e98" ++ String.ofList (List.replicate 63 '0')) "high-bit input ABI encoding changed"
  for invalid in ["", "00", "01", "-1", "+1", "0x1", " 1", toString (2 ^ 256 : Nat)] do
    rejected (Input.inputWord invalid) "noncanonical or overflowing input accepted"
  let identity ← function (.var 0)
  let mut source : Option String := none
  for input in Input.boundaryInputs do
    let saved ← get (Input.emitCase identity input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let emittedSource ← string saved "source"
    if let some prior := source then
      ensure (prior == emittedSource) "source text depends on runtime input"
    source := some emittedSource
    let checked ← get (Input.caseProgram saved)
    ensure (checked.program.check && checked.input == input) "applied original Core did not typecheck"
    ensure ((← field saved "directCore") == returned input) "identity did not use its runtime input"
    ensure ((← get (Input.replayCase saved 1000)) == saved) "imported case did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 17))
    ensure ((← get (Input.replayCase forged 1000)) == saved) "saved expected result was trusted"
    let exhausted ← get (Input.replayCase saved 0)
    ensure ((← string (← field exhausted "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed observation"
  let branch ← function (.ifE (.binary .wordGt (.var 0) (word 1)) (word 7) (word 0))
  ensure (Input.observe branch Word.zero 1000 == Input.observe branch (Word.ofNatModulo 1) 1000)
    "branch fixture should agree on zero and one"
  let _ ← get (Input.inputSensitive branch 1000)
  rejected (Input.inputSensitive (← function (word 7)) 1000) "constant generation candidate accepted"
  rejected (Input.inputSensitive identity 0) "fuel exhaustion passed the dynamic-input filter"
  let constant ← imported (word 7) Word.maximum
  ensure ((← field constant "directCore") == returned (Word.ofNatModulo 7))
    "imported constant functions must remain valid for shrinking"
  let oversized := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  rejected (Input.emitCase (← function oversized) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 1000) "oversized applied function escaped case limit"

private def generationChecks : IO Json := do
  let corpus := Input.generateCases (Seed.ofNat 0) 24 12 64 1000
  ensure (corpus == Input.generateCases (Seed.ofNat 0) 24 12 64 1000)
    "input generation is nondeterministic"
  ensure ((← string corpus "status") == "complete") "bounded input corpus did not complete"
  let rows ← cases corpus
  let attempted ← natural corpus "attempted"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (rows.size == 12 && attempted ≤ 64 && attempted == 3 + excluded.size)
    "function attempts and individual case counts were confused"
  for index in List.range rows.size do
    let saved := rows[index]!
    let checked ← get (Input.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure ((← natural origin "inputIndex") == index % 4 &&
      some checked.input == Input.boundaryInputs[index % 4]?) "boundary order changed"
    ensure ((← string provenance "profileVersion") == Input.profileVersion &&
      (← string provenance "generatorVersion") == generatorVersion) "profile version changed G0"
    ensure (checked.program.check && Wire.programNodes checked.program ≤ 512)
      "generated applied case escaped checker/node bound"
    ensure ((← get (Input.replayCase saved 1000)) == saved) "generated input replay differs"
    let suspended ← get (Input.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "generated replay confused its new observation budget with its validation budget"
    if index % 4 != 0 then
      ensure ((← string saved "source") == (← string rows[index - index % 4]! "source"))
        "one function's boundary cases emitted different source"
  let truncated := Input.generateCases (Seed.ofNat 0) 3 3 1 1000
  ensure ((← cases truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate the input group"
  let exhausted := Input.generateCases (Seed.ofNat 0) 3 5 1 1000
  ensure ((← cases exhausted).size == 4 && (← string exhausted "status") == "generation-exhausted")
    "attempt limit counted input cases instead of functions"
  for corpus in [Input.generateCases (Seed.ofNat 0) 2 1 3 1000,
      Input.generateCases (Seed.ofNat 0) 3 1 3 0] do
    ensure ((← cases corpus).isEmpty && (← natural corpus "attempted") == 3 &&
      (← string corpus "status") == "generation-exhausted") "failed generation lost its bound"
    ensure ((← get (corpus.getObjValAs? (Array Json) "excluded")).size == 3)
      "generation failures were not recorded"
  ensure ((← natural (Input.generateCases (Seed.ofNat 0) 3 0 100 1000) "attempted") == 0)
    "zero case request consumed attempts"
  ensure ((← cases (Input.generateCases (Seed.ofNat 0) 3 1 0 1000)).isEmpty)
    "zero attempt limit ignored"
  let resources ← get ((Input.generateCases (Seed.ofNat 0) 3 1 1 0).getObjValAs? (Array Json) "excluded")
  ensure ((← string resources[0]! "category") == "inconclusive-resource" &&
    (← string resources[0]! "code") == "boundary-out-of-fuel")
    "generation fuel exhaustion lost its resource classification"
  return corpus

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved := (← cases corpus)[0]!
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "abstractionVersion",
      "generatorVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Input.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (999 : Nat)), ("inputIndex", toJson (9 : Nat)),
      ("maxProgramNodes", toJson (513 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "unknown")] do
    rejected (Input.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} accepted"
  rejected (Input.replayCase (saved.setObjVal! "input" (toJson "1")) 1000)
    "input/program disagreement accepted"
  rejected (Input.replayCase (saved.setObjVal! "source" (toJson "forged")) 1000)
    "stale source accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"),
      ("signature", toJson "run()"), ("runtimePath", toJson ["Other"])] do
    rejected (Input.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "tampered ABI metadata accepted"
  rejected (Input.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000) "tampered features accepted"
  let identity ← function (.var 0)
  let badProgram := Wire.encodeProgram identity.program
  rejected (Input.caseProgram (saved.setObjVal! "program" badProgram))
    "bare lambda accepted as an applied input case"
  let invalidFunction : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 1) }
  rejected (Input.checkedFunction (Wire.encodeProgram invalidFunction)) "unbound parameter escaped sealing"
  let generated ← get ((generate {seed := Seed.ofNat 1, maxProgramNodes := 24}).mapError reprStr)
  let literalIndex := 1 % literalCount generated.program.body
  let some constant := CheckedWordFunction.fromProgram? generated.checkedProgram literalIndex |
    throw (IO.userError "constant boundary seed fixture changed")
  let forgedOrigin := Json.mkObj [("kind", toJson "input-generated"),
    ("seed", toJson "1"), ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson (24 : Nat)), ("literalIndex", toJson literalIndex),
    ("inputIndex", toJson (0 : Nat)), ("validationFuel", toJson (1000 : Nat))]
  let forged ← get (Input.emitCase constant Word.zero forgedOrigin 1000)
  rejected (Input.replayCase forged 1000)
    "replay accepted generated provenance for a function rejected by the input-sensitivity filter"

private def shrinkChecks : IO Unit := do
  let body := Wire.Expr.letE (.binary .wordAdd (.var 0) (word 17))
    (.ifE (.binary .wordGt (.var 0) (word 1))
      (.binary .wordXor (.var 0) (.var 1)) (word 99))
  let saved ← imported body Word.maximum
  let source ← get (Input.caseProgram saved)
  let shrunk ← get (Input.shrinkCases saved 100 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Input.shrinkCases saved 100 1000)))
    "input shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut changedInput := false
  let mut changedBody := false
  let mut constant := false
  for row in rows do
    let reduced ← get (Input.caseProgram row)
    ensure (reduced.program.check && Wire.programNodes reduced.program ≤ 512)
      "shrink escaped the applied lambda/checker/size boundary"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity source.program.body))
      "input reduction was not strictly smaller"
    let key := (Wire.encodeProgram reduced.program).compress
    ensure (!seen.contains key) "input shrink produced duplicate programs"
    seen := key :: seen
    ensure ((← get (Input.replayCase row 1000)) == row) "shrunk input did not replay"
    let emitted ← get ((Input.emit reduced.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "shrink retained stale emitted source"
    changedInput := changedInput || reduced.input != source.input
    changedBody := changedBody || Wire.encodeExpr reduced.function.body != Wire.encodeExpr source.function.body
    constant := constant || Wire.encodeExpr reduced.function.body == Wire.encodeExpr (word 0)
  ensure (changedInput && changedBody && constant) "shrinking missed input/body/constant candidates"
  ensure ((← cases (← get (Input.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "input shrink limit changed ordering"
  ensure ((← cases (← get (Input.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Input.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 100 1000)
    "shrinker accepted a stale source case"

def testSourceInputCases : IO Unit := do
  inputChecks
  let corpus ← generationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourceInputCases
end

section
-- leanmerge: from Solcore.Test.SourceInputEmitter
/-! Runtime-input profile checks: admission, capture-avoiding abstraction,
independent Core application and source formatting. These are printer tests,
not a source-to-Core meaning-preservation theorem. -/
set_option autoImplicit false

namespace Tests.SourceInputEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some function => pure function
  | none => throw (IO.userError "runtime-input fixture failed its profile or Core check")

private def sourceProgram (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some program => pure program
  | none => throw (IO.userError "literal-abstraction fixture is not a checked G0 program")

private def emitted (function : CheckedWordFunction) : IO EmittedProgram :=
  match Input.emit function with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"runtime-input fixture emission failed: {reprStr error}")

private def observe (function : CheckedWordFunction) (input expected : Nat) : IO Unit := do
  let argument := Word.ofNatModulo input
  ensure ((function.instantiate argument).check) "applied input function failed Core typing"
  match (function.instantiate argument).toCore.runStateful 1000 with
  | .done (.word actual) _ => ensure (actual.val == expected) "runtime-input Core result changed"
  | _ => throw (IO.userError "runtime-input Core application did not return a Word")

private def sameExpr (left right : Wire.Expr) : Bool := Wire.encodeExpr left == Wire.encodeExpr right

/-- A Word input below an outer local and both branch-local binders. -/
def scopedInput : Wire.Expr :=
  .letE (word 7) (.ifE (.binary .wordGt (.var 1) (word 0))
    (.letE (word 11) (.binary .wordAdd (.var 1) (.var 2)))
    (.letE (word 22) (.binary .wordSub (.var 2) (.var 1))))

/-- Reusable scalar inputs for frontend integration tests. Every enabled
primitive occurs in a computation whose result can depend on runtime input. -/
def fixtures : List (String × Wire.Expr) := [
  ("identity", .var 0),
  ("word-not", .unary .wordNot (.var 0)),
  ("word-add", .binary .wordAdd (.var 0) (word 1)),
  ("word-sub", .binary .wordSub (.var 0) (word 1)),
  ("word-mul", .binary .wordMul (.var 0) (word 2)),
  ("word-and", .binary .wordAnd (.var 0) (word 10)),
  ("word-or", .binary .wordOr (.var 0) (word 10)),
  ("word-xor", .binary .wordXor (.var 0) (word 10)),
  ("word-eq", .ifE (.binary .wordEq (.var 0) (.word Word.maximum)) (word 1) (word 0)),
  ("word-gt", .ifE (.binary .wordGt (.var 0) (word (2 ^ 255 - 1))) (word 1) (word 0)),
  ("bool-not", .ifE (.unary .boolNot (.binary .wordEq (.var 0) (word 0))) (word 1) (word 0)),
  ("scoped-input", scopedInput)]

private def admissionChecks : IO Unit := do
  let identity ← checked (.var 0)
  ensure identity.program.check "admitted function was not checked"
  let some readBack := CheckedWordFunction.ofProgram? identity.program |
    throw (IO.userError "canonical function program failed readmission")
  ensure (sameExpr readBack.body identity.body) "function readmission changed its body"
  for body in [(.var 1 : Wire.Expr), .bool true,
      .letE (word 0) (.var 2), .lambda .word .word (.var 0),
      .apply (.lambda .word .word (.var 0)) (word 0)] do
    ensure (CheckedWordFunction.ofBody? body).isNone
      "function profile admitted a host variable, wrong type or nested function"
  for program in [
      ({resultType := .word, dataDefinitions := [], body := word 0} : Wire.Program),
      {identity.program with resultType := .function .bool .word},
      {identity.program with body := .lambda .word .bool (.bool false)},
      {identity.program with dataDefinitions := [{constructorPayloadTypes := []}]}] do
    ensure (CheckedWordFunction.ofProgram? program).isNone
      "function profile admitted a different program shape"
  for input in [0, 1, Word.maximum.val, 2 ^ 255] do observe identity input input
  match (identity.instantiate Word.zero).toCore.runStateful 0 with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel function application was treated as completed")

private def abstractionChecks : IO Unit := do
  let original : Wire.Expr := .letE (word 7)
    (.letE (word 11) (.binary .wordAdd (.var 1) (word 22)))
  ensure ((wordLiterals original).map (fun value => value.val) == [7, 11, 22] && literalCount original == 3)
    "Word literal preorder changed"
  let expected : List Wire.Expr := [
    .letE (.var 0) (.letE (word 11) (.binary .wordAdd (.var 1) (word 22))),
    .letE (word 7) (.letE (.var 1) (.binary .wordAdd (.var 1) (word 22))),
    .letE (word 7) (.letE (word 11) (.binary .wordAdd (.var 1) (.var 2)))]
  let source ← sourceProgram original
  for (index, body) in expected.zipIdx |>.map (fun (body, index) => (index, body)) do
    let some actual := abstractWordLiteral original index |
      throw (IO.userError "in-range Word literal abstraction was rejected")
    ensure (sameExpr actual body) "Word literal abstraction captured or shifted an existing local"
    let some function := CheckedWordFunction.fromProgram? source index |
      throw (IO.userError "abstracted function failed checked admission")
    ensure (sameExpr function.body body) "checked abstraction changed the candidate"
    let _ ← emitted function
    observe function 5 (if index == 0 then 27 else if index == 1 then 29 else 12)
  for index in [3, 4, 100] do
    ensure ((abstractWordLiteral original index).isNone &&
      (CheckedWordFunction.fromProgram? source index).isNone)
      "out-of-range literal selection was silently replaced"
  let initializer : Wire.Expr := .letE (word 7)
    (.letE (.binary .wordAdd (.var 0) (word 11)) (.binary .wordSub (.var 0) (.var 1)))
  let some changed := CheckedWordFunction.fromProgram? (← sourceProgram initializer) 1 |
    throw (IO.userError "initializer abstraction failed")
  observe changed 5 5
  let branches : Wire.Expr := .ifE (.bool true) (word 1) (.letE (word 2) (word 3))
  ensure ((wordLiterals branches).map (fun value => value.val) == [1, 2, 3]) "literal traversal skipped an untaken branch"
  let some last := abstractWordLiteral branches 2 | throw (IO.userError "untaken literal was not selectable")
  ensure (sameExpr last (.ifE (.bool true) (word 1) (.letE (word 2) (.var 1))))
    "untaken branch literal acquired the wrong parameter index"

private def executionChecks : IO Unit := do
  for (label, body) in fixtures do
    let function ← checked body
    let first ← emitted function
    ensure (first == (← emitted function)) s!"input emission is not deterministic: {label}"
    ensure (first.contractName == "SynthesizedInput" && first.methodName == "run" &&
      first.methodSignature == "run(uint256)" && first.deployPath == ["SynthesizedInputDeploy"] &&
      first.runtimePath == ["SynthesizedInputDeploy", "SynthesizedInput"])
      s!"input wrapper metadata changed: {label}"
  for (label, input, expected) in [
      ("word-not", 0, Word.maximum.val), ("word-not", Word.maximum.val, 0),
      ("word-add", Word.maximum.val, 0), ("word-sub", 0, Word.maximum.val),
      ("word-mul", 2 ^ 255, 0), ("word-and", 252, 8),
      ("word-or", 252, 254), ("word-xor", 252, 246),
      ("word-eq", Word.maximum.val, 1), ("word-eq", 0, 0),
      ("word-gt", 2 ^ 255, 1), ("word-gt", 1, 0),
      ("bool-not", 0, 0), ("bool-not", 1, 1),
      ("scoped-input", 0, Word.maximum.val - 6), ("scoped-input", 1, 8)] do
    let some (_, body) := fixtures.find? (fun entry => entry.1 == label) |
      throw (IO.userError s!"missing runtime-input fixture {label}")
    observe (← checked body) input expected
  for (body, expected) in [
      (.unary .wordClz (.var 0), EmitError.unsupportedUnary .wordClz),
      (.binary .wordDiv (.var 0) (word 0), .unsupportedBinary .wordDiv),
      (.ternary .wordAddMod (.var 0) (word 1) (word 2), .unsupportedTernary .wordAddMod)] do
    match Input.emit (← checked body) with
    | .error actual => ensure (actual == expected) "unsupported input operation returned the wrong error"
    | .ok _ => throw (IO.userError "unsupported input operation was silently emitted")

private def formattingChecks : IO Unit := do
  let identityExpected := String.intercalate "\n" [
    "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedInput {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        return uint256(sc_input);", "    }", "}", ""]
  ensure ((← emitted (← checked (.var 0))).source == identityExpected)
    "input emission no longer reads the runtime ABI parameter"
  let bindingExpected := String.intercalate "\n" [
    "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
    "contract SynthesizedInput {",
    "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
    "        let sc_v2: word = (sc_v1 + sc_input);",
    "        return uint256(sc_v2);", "    }", "}", ""]
  ensure ((← emitted (← checked (.letE (word 7) (.binary .wordAdd (.var 0) (.var 1))))).source == bindingExpected)
    "local binding hid or renamed the runtime input"
  ensure (Input.emitterVersion == "solcore-source-input-v2" &&
    Input.wrapperVersion == "solcore-word-input-contract-v1" && Input.selector == "0xa444f5e9" &&
    wordFunctionVersion == "core-word-function-v1" && abstractionVersion == "word-literal-preorder-v1")
    "input-profile provenance changed"

def testSourceInputEmitter : IO Unit := do
  admissionChecks
  abstractionChecks
  executionChecks
  formattingChecks

end Tests.SourceInputEmitter
end

section
-- leanmerge: from Solcore.Test.SourceIntegerCases
/-! The `runtime-checked-arithmetic` and `runtime-shifts` profiles. Their Core
references compute each operation exactly on Core's integers, range-check or
wrap it, and raise `Panic(code)` or std's `DirtyHigherBitsForInteger()` as
revert data; they agree with the plans' direct interpreter over Lean integers
on generated plans, and four fixtures' sources and results are golden, the
results from the corpus validator's separate Python model. Admission refuses
types, inputs, amounts, helpers, groups and steps outside each profile;
generation draws every shape and replays exactly; tampering is refused, and
reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceIntegerCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Integers
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.Integers (Profile Observed)

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

/-- The eight boundary inputs, then four more. -/
private def inputs : List Nat :=
  boundaryWords ++ [3, 7, 2 ^ 128 + 5, 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef]

/-- A returned Word in decimal, revert data in hex. -/
private def observedText : Observed → String
  | .word word => toString word.val
  | .reverted data => Integers.hexBytes data

/-- The reference's outcome at an input. -/
private def referenceText (plan : Plan) (input : Nat) : String :=
  match (plan.applied (Word.ofNatModulo input)).toCore.runStateful fuel with
  | .done value _ => match Observed.ofValue? value with
      | some observed => observedText observed
      | none => "invalid-result"
  | .outOfFuel _ => "out-of-fuel"
  | .fault _ _ => "core-fault"

/-- The interpreter's outcome at an input, as revert data for a revert. -/
private def interpreterText (plan : Plan) : Nat → String := fun input =>
  match plan.outcome input with
  | .word value => toString value
  | .panic code => Integers.hexBytes ([0x4e, 0x48, 0x7b, 0x71] ++ Integers.wordBytes code)
  | .dirty => "0x6cc54a63"

/-! Fixtures. The first checked arithmetic fixture takes an `int8` argument and
returns `int8`: an inline addition, a checked division helper, a block with
`MIN / -1`, a negation, an unchecked multiplication helper and a defaulted
`uint256` literal that wraps, then a lambda with an unchecked body, a compound
remainder and a checked defaulted subtraction. The second is `uint64` over
`run(uint256)`: a compound product, a defaulted addition, a block with a
subtraction from a zero literal, a checked helper and a checked lambda, then a
remainder and a negation. The shift fixtures shift `int16` values by a Word
and a `uint8` amount and by literal amounts in and out of a block, and Words
by `uint256`, `uint16` and `uint128` amounts. -/

private def arithmeticA : Plan := {
  value := .int ⟨true, 1⟩, abi := true, raw := true, inputs := [0, 128, 127], amounts := [],
  helpers := [{op := .mul, unchecked := true}, {op := .div, unchecked := false}],
  groups := [
    {unchecked := false, steps := [.assign (.binary .add (.input 0) (.literal 4)), .assign (.call 1 (.input 1) (.input 2))]},
    {unchecked := true, steps := [.assign (.binary .div (.input 1) (.literal 2)), .assign (.neg (.input 1)),
      .assign (.call 0 (.var 0) (.input 2)), .default {initial := 1, test := .gt 7, chosen := 7, op := .add, operand := 1}]},
    {unchecked := false, steps := [.assign (.apply .sub true (.var 2) (.literal 0)), .assign (.compound .mod (.var 3) (.input 0)),
      .default {initial := 7, test := .bits 1 0, chosen := 0, op := .sub, operand := 1}]}]}

private def arithmeticB : Plan := {
  value := .int ⟨false, 8⟩, abi := false, raw := false, inputs := [0, 1, 2 ^ 64 - 1], amounts := [],
  helpers := [{op := .sub, unchecked := false}],
  groups := [
    {unchecked := false, steps := [.assign (.compound .mul (.input 0) (.input 1)),
      .default {initial := 1, test := .eq 255, chosen := 7, op := .add, operand := 1}]},
    {unchecked := true, steps := [.assign (.binary .sub (.literal 0) (.input 1)), .assign (.call 0 (.literal 7) (.var 1)),
      .assign (.apply .add false (.var 0) (.input 0))]},
    {unchecked := false, steps := [.assign (.binary .mod (.var 2) (.input 2)), .assign (.neg (.var 4))]}]}

private def shiftA : Plan := {
  value := .int ⟨true, 2⟩, abi := false, raw := false, inputs := [0, 2 ^ 15],
  amounts := [{type := .word, offset := 0}, {type := .int ⟨false, 1⟩, offset := 7}], helpers := [],
  groups := [
    {unchecked := false, steps := [.shift {direction := .left, compound := false, value := .input 0, amount := .input 1},
      .shift {direction := .right, compound := false, value := .input 1, amount := .literal 16}]},
    {unchecked := true, steps := [.shift {direction := .left, compound := true, value := .var 0, amount := .input 0},
      .shift {direction := .right, compound := false, value := .literal 0, amount := .input 1}]},
    {unchecked := false, steps := [.shift {direction := .right, compound := true, value := .var 1, amount := .literal 5}]}]}

private def shiftB : Plan := {
  value := .word, abi := false, raw := false, inputs := [0, 3],
  amounts := [{type := .int ⟨false, 32⟩, offset := 255}, {type := .int ⟨false, 2⟩, offset := 256},
    {type := .int ⟨false, 16⟩, offset := 0}], helpers := [],
  groups := [{unchecked := false, steps := [
    .shift {direction := .left, compound := false, value := .input 0, amount := .input 0},
    .shift {direction := .right, compound := false, value := .input 1, amount := .input 1},
    .shift {direction := .right, compound := true, value := .var 0, amount := .input 2},
    .shift {direction := .left, compound := false, value := .literal 7, amount := .literal 14}]}]}


private def arithmeticASource : String :=
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_h0(sc_p: int8, sc_q: int8) returns (int8) {\n    unchecked {\n        return (sc_p * sc_q);\n    }\n}\n\nfunction sc_h1(sc_p: int8, sc_q: int8) returns (int8) {\n    return (sc_p / sc_q);\n}\n\nfunction sc_apply(sc_f: function (int8) returns (int8), sc_v: int8) returns (int8) {\n    return sc_f(sc_v);\n}\n\ncontract SynthesizedCheckedArithmetic {\n    function run(input: int8) public returns (int8) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: int8 = input;\n        let sc_a1: int8 = Typedef.abs(sc_signextend(0, (sc_x + 128)));\n        let sc_a2: int8 = Typedef.abs(sc_signextend(0, (sc_x + 127)));\n        let sc_acc: word = 0;\n        let sc_v0: int8 = (sc_a0 + 1);\n        let sc_v1: int8 = sc_h1(sc_a1, sc_a2);\n        let sc_v2: int8 = 0;\n        let sc_v3: int8 = 0;\n        let sc_v4: int8 = 0;\n        let sc_d0 = 1;\n        if (sc_x > 7) {\n            sc_d0 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        }\n        let sc_e0 = 0;\n        unchecked {\n            sc_v2 = (sc_a1 / (-1));\n            sc_v3 = (-sc_a1);\n            sc_v4 = sc_h0(sc_v0, sc_a2);\n            sc_e0 = (sc_d0 + 1);\n        }\n        let sc_d1 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        if ((sc_x & 1) == 0) {\n            sc_d1 = 0;\n        }\n        let sc_v5: int8 = sc_apply(lam (sc_l: int8) -> int8 {\n            unchecked {\n                return (sc_l - (-128));\n            }\n        }, sc_v2);\n        let sc_v6: int8 = sc_v3;\n        sc_v6 %= sc_a0;\n        let sc_e1 = (sc_d1 - 1);\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v5));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v6));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e1));\n        return Typedef.abs(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def arithmeticAResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "115792089237316195423570985008687907853269984665640564039457584007913129639831",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x6cc54a63",
    "0x6cc54a63",
    "34",
    "0x6cc54a63",
    "0x6cc54a63",
    "115792089237316195423570985008687907853269984665640564039457584007913129639845",
    "115792089237316195423570985008687907853269984665640564039457584007913129639885",
    "0x6cc54a63",
    "0x6cc54a63"]

private def arithmeticBSource : String :=
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.unchecked.unsigned;\nimport * from std.dispatch;\n\nfunction sc_h0(sc_p: uint64, sc_q: uint64) returns (uint64) {\n    return (sc_p - sc_q);\n}\n\nfunction sc_apply(sc_f: function (uint64) returns (uint64), sc_v: uint64) returns (uint64) {\n    return sc_f(sc_v);\n}\n\ncontract SynthesizedCheckedArithmetic {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: uint64 = Typedef.abs((sc_x & 0xffffffffffffffff));\n        let sc_a1: uint64 = Typedef.abs(((sc_x + 1) & 0xffffffffffffffff));\n        let sc_a2: uint64 = Typedef.abs(((sc_x + 18446744073709551615) & 0xffffffffffffffff));\n        let sc_acc: word = 0;\n        let sc_d0 = 1;\n        if (sc_x == 255) {\n            sc_d0 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        }\n        let sc_v0: uint64 = sc_a0;\n        sc_v0 *= sc_a1;\n        let sc_e0 = (sc_d0 + 1);\n        let sc_v1: uint64 = 0;\n        let sc_v2: uint64 = 0;\n        let sc_v3: uint64 = 0;\n        unchecked {\n            sc_v1 = (0 - sc_a1);\n            sc_v2 = sc_h0(18446744073709551615, sc_v1);\n            sc_v3 = sc_apply(lam (sc_l: uint64) -> uint64 {\n                return (sc_l + sc_a0);\n            }, sc_v0);\n        }\n        let sc_v4: uint64 = (sc_v2 % sc_a2);\n        let sc_v5: uint64 = (-sc_v4);\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v5));\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def arithmeticBResults : List String := [
    "26959943495939220800718331828086778140708015150586758381788765843113",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "10601109357008446254964315403763482149948774975692891568105106563444499231",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "26959943495939220800718331828086778140708015150586758381788765843113",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"]

private def shiftASource : String :=
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\ncontract SynthesizedShifts {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: int16 = Typedef.abs(sc_signextend(1, sc_x));\n        let sc_a1: int16 = Typedef.abs(sc_signextend(1, (sc_x + 32768)));\n        let sc_k0: word = sc_x;\n        let sc_k1: uint8 = Typedef.abs(((sc_x + 7) & 0xff));\n        let sc_acc: word = 0;\n        let sc_v0: int16 = (sc_a0 << sc_k1);\n        let sc_v1: int16 = (sc_a1 >> 300);\n        let sc_v2: int16 = 0;\n        let sc_v3: int16 = 0;\n        unchecked {\n            sc_v2 = sc_v0;\n            sc_v2 <<= sc_k0;\n            sc_v3 = ((-32768) >> sc_k1);\n        }\n        let sc_v4: int16 = sc_v1;\n        sc_v4 >>= 15;\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def shiftAResults : List String := [
    "115792089237316195423570985008687907853268655437643201475389458753201454373290",
    "115792089237316195423570984634543488104466189583693770850429139307045459162154",
    "115792089237316195423570983512110228858058792021838051335306591137569476660202",
    "115792089237316195423570961156981148867111457248327539795385640839944169645162",
    "47890485727846714300077608985593429736312073170672042",
    "93536104937200616463487512398745113151610115063232",
    "115792089237316195423570985008687907853268655437643201475389458753201454373290",
    "93536104937200616463487512398745113151610115063232",
    "115792089237316195423570980518954870867639065190272316896590392323894338944394",
    "23945242863923356485424805811514680805719995771011412",
    "115792089237316195423570955077134327949071387121639233876953295458678879201058",
    "115792089237316195423570985008687907853269984665640564039457584006813618011725"]

private def shiftBSource : String :=
  "pragma solcore;\nimport * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\ncontract SynthesizedShifts {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: word = sc_x;\n        let sc_a1: word = (sc_x + 3);\n        let sc_k0: uint256 = Typedef.abs((sc_x + 255));\n        let sc_k1: uint16 = Typedef.abs(((sc_x + 256) & 0xffff));\n        let sc_k2: uint128 = Typedef.abs((sc_x & 0xffffffffffffffffffffffffffffffff));\n        let sc_acc: word = 0;\n        let sc_v0: word = (sc_a0 << sc_k0);\n        let sc_v1: word = (sc_a1 >> sc_k1);\n        let sc_v2: word = sc_v0;\n        sc_v2 >>= sc_k2;\n        let sc_v3: word = (115792089237316195423570985008687907853269984665640564039457584007913129639935 << 256);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v0);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v1);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v2);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v3);\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def shiftBResults : List String := [
    "0",
    "0",
    "0",
    "0",
    "0",
    "28948022309329048855892746252171976963317496166410141009864396001978282409984",
    "0",
    "1208925820571204291060521",
    "0",
    "0",
    "0",
    "0"]

private def fixtures : List (String × Profile × Plan × String × List String) := [
  ("arithmeticA", CheckedArithmetic.profile, arithmeticA, arithmeticASource, arithmeticAResults),
  ("arithmeticB", CheckedArithmetic.profile, arithmeticB, arithmeticBSource, arithmeticBResults),
  ("shiftA", Shifts.profile, shiftA, shiftASource, shiftAResults),
  ("shiftB", Shifts.profile, shiftB, shiftBSource, shiftBResults)]

private def fixtureChecks : IO Unit := do
  for (name, profile, plan, source, results) in fixtures do
    ensure (profile.admitted plan) (name ++ " is not admitted")
    ensure (plan.applied Word.zero).check (name ++ " failed the Core checker")
    ensure ((profile.emit plan).source == source) (name ++ " source differs from its golden text")
    ensure (results.length == inputs.length) (name ++ " golden results are incomplete")
    for (input, expected) in inputs.zip results do
      ensure (referenceText plan input == expected) s!"{name} reference differs at {input}"
      ensure (interpreterText plan input == expected) s!"{name} interpreter differs at {input}"
  let texts := fixtures.flatMap fun (_, _, _, _, results) => results
  for expected in ["0x6cc54a63", "0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ "11",
      "0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ "12"] do
    ensure (texts.contains expected) ("the fixtures reach no " ++ expected)

/-! Admission. -/

private def binary : Step := .assign (.binary .add (.input 0) (.input 0))
private def shiftStep : Step := .shift {direction := .left, compound := false, value := .input 0, amount := .literal 1}
private def defaulted : Step := .default {initial := 0, test := .eq 0, chosen := 1, op := .add, operand := 1}
private def checked (steps : List Step) : List Group := [{unchecked := false, steps}]

private def arithmeticRefusals : List (String × Plan) :=
  let base : Plan := {
    value := .int ⟨false, 1⟩, abi := false, raw := false, inputs := [0], amounts := [],
    helpers := [], groups := checked [binary]}
  [("a Word type", {base with value := .word}), ("a 24-bit type", {base with value := .int ⟨false, 3⟩}),
    ("no input", {base with inputs := []}), ("four inputs", {base with inputs := [0, 1, 3, 1]}),
    ("a first offset", {base with inputs := [1]}), ("an offset outside the table", {base with inputs := [0, 2]}),
    ("an amount", {base with amounts := [{type := .word, offset := 0}]}),
    ("three helpers", {base with
      helpers := List.replicate 3 {op := .add, unchecked := false}
      groups := checked [.assign (.call 0 (.input 0) (.input 0)), .assign (.call 1 (.input 0) (.input 0)),
        .assign (.call 2 (.input 0) (.input 0))]}),
    ("a helper nothing calls", {base with helpers := [{op := .add, unchecked := false}]}),
    ("a call past the helpers", {base with groups := checked [.assign (.call 0 (.input 0) (.input 0))]}),
    ("a 256-bit T result", {base with value := .int ⟨false, 32⟩, raw := true}),
    ("no group", {base with groups := []}), ("an empty group", {base with groups := checked []}),
    ("adjacent blocks", {base with groups := [{unchecked := true, steps := [binary]}, {unchecked := true, steps := [binary]}]}),
    ("four blocks", {base with groups := (List.range 7).map fun index => {unchecked := index % 2 == 0, steps := [binary]}}),
    ("eleven steps", {base with groups := checked (List.replicate 11 binary)}),
    ("a variable before it exists", {base with groups := checked [.assign (.binary .add (.var 0) (.input 0))]}),
    ("an input past the inputs", {base with groups := checked [.assign (.binary .add (.input 1) (.input 0))]}),
    ("a literal past the table", {base with groups := checked [.assign (.binary .add (.input 0) (.literal 8))]}),
    ("a negated literal", {base with groups := checked [.assign (.neg (.literal 0))]}),
    ("a lambda block inside a block",
      {base with groups := [{unchecked := true, steps := [.assign (.apply .add true (.input 0) (.input 0))]}]}),
    ("only defaulted results", {base with groups := checked [defaulted]}),
    ("three defaulted results", {base with groups := checked [binary, defaulted, defaulted, defaulted]}),
    ("a defaulted literal past the table", {base with groups := checked [binary,
      .default {initial := 8, test := .eq 0, chosen := 1, op := .add, operand := 1}]}),
    ("a test constant outside the table", {base with groups := checked [binary,
      .default {initial := 0, test := .eq 3, chosen := 1, op := .add, operand := 1}]}),
    ("a mask outside the table", {base with groups := checked [binary,
      .default {initial := 0, test := .bits 2 0, chosen := 1, op := .add, operand := 1}]}),
    ("a bit value above its mask", {base with groups := checked [binary,
      .default {initial := 0, test := .bits 1 2, chosen := 1, op := .add, operand := 1}]}),
    ("a shift", {base with groups := checked [shiftStep]})]

private def arithmeticControls : List Plan :=
  let base : Plan := {
    value := .int ⟨true, 32⟩, abi := true, raw := false, inputs := [0, 2 ^ 255 - 1, 2 ^ 256 - 1],
    amounts := [], helpers := [{op := .div, unchecked := true}, {op := .mod, unchecked := false}],
    groups := [{unchecked := true, steps := [.assign (.call 0 (.input 2) (.literal 10)), defaulted]},
      {unchecked := false, steps := [.assign (.call 1 (.var 0) (.input 1)), defaulted]}, {unchecked := true, steps := [binary]},
      {unchecked := false, steps := [binary]}, {unchecked := true, steps := [.assign (.neg (.var 1))]}]}
  [base, {base with
    value := .int ⟨false, 1⟩, inputs := [0, 1, 255], raw := true, abi := false
    groups := checked (List.replicate 10 binary), helpers := []},
    {base with groups := [{unchecked := false, steps := [.assign (.apply .mod true (.input 0) (.literal 10)),
      .assign (.call 0 (.input 0) (.input 0)), .assign (.call 1 (.var 1) (.var 0))]}]}]

private def shiftRefusals : List (String × Plan) :=
  let base : Plan := {
    value := .word, abi := false, raw := false, inputs := [0], amounts := [{type := .word, offset := 0}],
    helpers := [], groups := checked [shiftStep]}
  [("run(T)", {base with abi := true}), ("a T result", {base with value := .int ⟨true, 1⟩, raw := true}),
    ("no amount", {base with amounts := []}),
    ("four amounts", {base with amounts := List.replicate 4 {type := .word, offset := 0}}),
    ("a signed amount", {base with amounts := [{type := .int ⟨true, 1⟩, offset := 0}]}),
    ("an amount offset outside the table", {base with amounts := [{type := .word, offset := 2}]}),
    ("an amount past the amounts", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .input 0, amount := .input 1}]}),
    ("an amount literal past the table", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .input 0, amount := .literal 17}]}),
    ("a helper", {base with helpers := [{op := .add, unchecked := false}]}),
    ("an operation", {base with groups := checked [binary]}),
    ("a defaulted result", {base with groups := checked [shiftStep, defaulted]}),
    ("a value past the literals", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .literal 8, amount := .literal 1}]})]

private def shiftControls : List Plan :=
  let base : Plan := {
    value := .int ⟨true, 16⟩, abi := false, raw := false, inputs := [0, 1, 2 ^ 128 - 1],
    amounts := [{type := .int ⟨false, 32⟩, offset := 300}, {type := .int ⟨false, 1⟩, offset := 255}, {type := .word, offset := 0}],
    helpers := [], groups := [{unchecked := true, steps := List.replicate 4 shiftStep},
      {unchecked := false, steps := List.replicate 6 shiftStep}]}
  [base, {base with value := .word, inputs := [0], amounts := [{type := .int ⟨false, 2⟩, offset := 0}]}]

private def admissionChecks : IO Unit := do
  for (label, plan) in arithmeticRefusals do
    ensure (!plan.arithmeticAdmitted) ("checked arithmetic admission accepted " ++ label)
  for (label, plan) in shiftRefusals do
    ensure (!plan.shiftAdmitted) ("shift admission accepted " ++ label)
  for plan in arithmeticControls do
    ensure plan.arithmeticAdmitted ("checked arithmetic admission refused a control: " ++ reprStr plan)
    ensure (!plan.shiftAdmitted) "shift admission accepted a checked arithmetic plan"
  for plan in shiftControls do
    ensure plan.shiftAdmitted ("shift admission refused a control: " ++ reprStr plan)
    ensure (!plan.arithmeticAdmitted) "checked arithmetic admission accepted a shift plan"

/-! The reference against the interpreter. -/

private def modelChecks : IO Unit := do
  let mut outcomes := 0
  let mut reverts := 0
  let mut panics : List String := []
  for (generate, admitted) in [(generateArithmetic, Plan.arithmeticAdmitted), (generateShifts, Plan.shiftAdmitted)] do
    for seed in List.range 200 do
      let plan := (generate (UInt64.ofNat seed)).fit Integers.defaultNodes
      ensure (admitted plan) s!"seed {seed} drew a plan outside its profile"
      ensure (plan.applied Word.zero).check s!"seed {seed} failed the Core checker"
      for input in inputs do
        let expected := interpreterText plan input
        ensure (referenceText plan input == expected) s!"seed {seed}: reference and interpreter differ at {input}"
        outcomes := outcomes + 1
        if expected.startsWith "0x" then
          reverts := reverts + 1
          unless panics.contains expected do panics := panics ++ [expected]
  ensure (outcomes == 4800) "the model checks lost outcomes"
  ensure (reverts > 1000 && panics.length == 3) s!"the model checks reached {reverts} reverts of {panics.length} kinds"

/-! Generation and replay. -/

private def shapeValues (shapes : List (String × List String)) : List (String × String) :=
  shapes.flatMap fun (dimension, values) => values.map (dimension, ·)

private def generationChecks : IO Unit := do
  for (profile, count, recorded) in [(CheckedArithmetic.profile, 1000, ["typeOutcomes"]), (Shifts.profile, 300, [])] do
    let mut seen : List (String × String) := []
    for seed in List.range count do
      let plan := (profile.generate (UInt64.ofNat seed)).fit Integers.defaultNodes
      ensure (plan == (profile.generate (UInt64.ofNat seed)).fit Integers.defaultNodes) "generation is not deterministic"
      for value in shapeValues (profile.shapes plan) do
        unless seen.contains value do seen := seen ++ [value]
    let all := shapeValues (if profile.label == "shift" then shiftShapeInventory else arithmeticShapeInventory)
    for value in seen do
      ensure (all.contains value) s!"{profile.label}: {value.1} {value.2} is outside the inventory"
    for value in all do
      unless recorded.contains value.1 do
        ensure (seen.contains value) s!"{profile.label}: {value.1} {value.2} is never drawn"
    let corpus := profile.generateCases (Seed.ofNat 1) Integers.defaultNodes 64 400 fuel
    let cases ← expect (corpus.getObjValAs? (Array Json) "cases")
    ensure (cases.size == 64) (profile.label ++ ": generation did not complete 64 cases")
    for case in cases do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a generated case does not replay")
    let seeded := profile.generateCases (Seed.ofNat 7) Integers.defaultNodes 24 400 fuel .seeded .nonIdentity
    for case in ← expect (seeded.getObjValAs? (Array Json) "cases") do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a seeded case does not replay")
    let small := (List.range 200).any fun seed =>
      ((profile.generate (UInt64.ofNat seed)).fit 256).stepCount < (profile.generate (UInt64.ofNat seed)).stepCount
    ensure small (profile.label ++ ": a 256-node budget never drops a step")

/-! Tampering and reduction. -/

private def setObj (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | other => other

private def tamperChecks : IO Unit := do
  for (name, profile, plan, _, _) in fixtures do
    let some checkedPlan := Integers.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError name)
    let case ← expect (profile.emitCase checkedPlan (Word.ofNatModulo 2) (Json.mkObj [("kind", toJson "imported")]) fuel)
    ensure ((profile.replayCase case fuel).toOption == some case) (name ++ " does not replay")
    let source ← expect (case.getObjValAs? String "source")
    let provenance ← expect (case.getObjVal? "provenance")
    let contract ← expect (case.getObjVal? "contract")
    for (label, tampered) in [
        ("source", setObj case "source" (toJson (source ++ "\n"))),
        ("input", setObj case "input" (toJson "3")),
        ("program", setObj case "program" (Json.mkObj [])),
        ("plan", setObj case profile.planKey (profile.planJson {plan with raw := !plan.raw})),
        ("shapes", setObj case "provenance" (setObj provenance profile.shapesKey (Json.mkObj []))),
        ("generator version", setObj case "provenance" (setObj provenance "generatorVersion" (toJson "core-halt-v1"))),
        ("wrapper", setObj case "contract" (setObj contract "name" (toJson "SynthesizedRevertData")))] do
      ensure (profile.replayCase tampered fuel).toOption.isNone (name ++ ": replay accepted an altered " ++ label)
    let forged := setObj case "directCore" (Json.mkObj [("stage", toJson "execution"), ("status", toJson "returned"),
      ("word", toJson "7")])
    ensure ((profile.replayCase forged fuel).toOption == some case) (name ++ ": replay trusted the saved observation")
    let shrunk ← expect (profile.shrinkCases case 64 fuel)
    let candidates ← expect (shrunk.getObjValAs? (Array Json) "cases")
    ensure (candidates.size ≥ 8) (name ++ " has too few reductions")
    for candidate in candidates do
      ensure ((profile.replayCase candidate fuel).toOption == some candidate) (name ++ ": a reduction does not replay")
  let some source := Integers.CheckedPlan.ofPlan? (profile := CheckedArithmetic.profile) arithmeticA | throw (IO.userError "A")
  let reduced := (Integers.reductions ⟨source, Word.ofNatModulo 2⟩).map (·.candidate.plan.plan)
  for (label, expected) in [("run(uint256)", {arithmeticA with abi := false}), ("a uint256 result", {arithmeticA with raw := false})] do
    ensure (reduced.contains expected) ("no reduction to " ++ label)
  let blocked (plan : Plan) : Nat := (plan.steps.filter (·.1)).length
  ensure (reduced.any fun plan => blocked plan < blocked arithmeticA) "no reduction moves a step out of its block"
  ensure (reduced.any fun plan => plan.inputs.length < arithmeticA.inputs.length) "no reduction removes an input"
  ensure (reduced.any fun plan => plan.helpers.any (·.unchecked) != arithmeticA.helpers.any (·.unchecked))
    "no reduction checks a helper"

def testSourceIntegerCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceIntegerCases
end

section
-- leanmerge: from Solcore.Test.SourceModuleCases
/-! Modules cases retain original ASTs and all four source files, execute the Core composition
independently, reject changed provenance, and shrink either typed component. -/
set_option autoImplicit false

namespace Tests.SourceModuleCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.Modules (CheckedPlan)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO Aggregates.CheckedDAG :=
  match Aggregates.CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "module step fixture failed checked admission")
private def constant (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? {resultType := .word, dataDefinitions := [], body} with
  | some value => pure value
  | none => throw (IO.userError "constant fixture is not a checked closed G0 Word")
private def constantBody : Wire.Expr :=
  .letE (.binary .wordAdd (word 2) (word 3))
    (.ifE (.binary .wordGt (.var 0) (word 4))
      (.binary .wordMul (.var 0) (word 2)) (word 0))
private def plan (fixed : CheckedWordProgram) (step : Aggregates.CheckedDAG) : IO CheckedPlan :=
  match CheckedPlan.ofParts? fixed step with
  | some value => pure value
  | none => throw (IO.userError "module plan fixture failed checked admission")
private def imported (value : CheckedPlan) (input : Word) : IO Json :=
  get (Modules.emitCase value input (Json.mkObj [("kind", toJson "imported")]) 10000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

/-- One private step cell is followed by the wrapper's mutable capture cell.
The entry differs from the last helper and must not be discarded by the wrapper. -/
private def privateStep : Wire.Expr :=
  .letE (.newCell .word (.var 0))
    (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 2)))
      (.loadCell (.var 1)))

private def expected (k input stepOffset : Word) : Word :=
  let left := (((input.add k).add stepOffset).mul (Word.ofNatModulo 2)).add input |>.add (Word.ofNatModulo 1)
  let right := ((input.bitXor k).mul (Word.ofNatModulo 2)).add input |>.add (Word.ofNatModulo 3)
  let selected := if input.bitAnd (Word.ofNatModulo 1) == Word.ofNatModulo 1 then left else right
  ((selected.add left).add (right.mul (Word.ofNatModulo 3))).add k

private def checkBundle (saved : Json) : IO Unit := do
  let bundle ← field saved "sourceBundle"
  ensure ((← string bundle "schema") == "solcore-lean.source-bundle.v1" &&
    (← string bundle "entry") == "case.sol") "module bundle schema/entry changed"
  let files ← get (bundle.getObjValAs? (Array Json) "files")
  let paths ← files.toList.mapM fun file => string file "path"
  ensure (paths == ["case.sol", "common.sol", "left.sol", "right.sol"])
    "module bundle is not the exact sorted four-file source"
  ensure ((← string files[0]! "source") == (← string saved "source"))
    "single source alias differs from case.sol bytes"

private def referenceChecks : IO Unit := do
  let fixed ← constant constantBody
  ensure (Solcore.Synthesis.Source.observe fixed 10000 == returned (Word.ofNatModulo 10))
    "independent closed constant golden failed"
  let graph ← checked [privateStep] (.binary .wordSub entry (word 1))
  let value ← plan fixed graph
  ensure (Wire.programNodes (value.instantiate Word.zero) ==
    Wire.programNodes fixed.program + Wire.programNodes graph.program +
    Solcore.Synthesis.Core.Modules.appliedOverhead)
    "module whole node budget omitted one original expression"
  let mut source : Option Json := none
  for input in Modules.boundaryInputs do
    ensure (Modules.observe value input 10000 == returned (expected (Word.ofNatModulo 10) input (Word.ofNatModulo 1)))
      s!"module provider/capture/selection mismatch: input {input.val}"
    match (value.instantiate input).toCore.runStateful 10000 with
    | .done (.word _) store =>
        ensure (store == [.word (input.add (Word.ofNatModulo 12)),
          .word (input.add (Word.ofNatModulo 12)),
          .word ((input.bitXor (Word.ofNatModulo 10)).add (Word.ofNatModulo 2))])
          "module composition changed provider order or shared a private capture cell"
    | _ => throw (IO.userError "checked module reference did not return")
    let saved ← imported value input
    checkBundle saved
    let current ← field saved "sourceBundle"
    if let some previous := source then ensure (current == previous) "module bundle depends on runtime input"
    source := some current
    let admitted ← get (Modules.caseProgram saved)
    ensure (admitted.program.check && admitted.input == input &&
      Wire.encodeProgram admitted.plan.constant.program == Wire.encodeProgram fixed.program)
      "module case lost one original checked expression"
    ensure ((← get (Modules.replayCase saved 10000)) == saved) "imported module case did not replay"
    ensure ((← get (Modules.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 10000)) == saved)
      "module replay trusted its stored expected result"
    let low ← get (Modules.replayCase saved 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "module fuel exhaustion was treated as completion"
  let identity ← checked [.var 0]
  let literal ← constant (word 4)
  let literalPlan ← plan literal identity
  ensure (!(Modules.inputSensitive literalPlan 10000).isOk)
    "generated constant without an operation was admitted"
  ensure ((Modules.emitCase literalPlan Word.zero (Json.mkObj [("kind", toJson "imported")]) 10000).isOk)
    "imported literal constant should remain supported"
  let constantStep ← checked [word 4]
  let constantPlan ← plan fixed constantStep
  ensure (!(Modules.inputSensitive constantPlan 10000).isOk)
    "generated module plan lost the step's input-sensitive requirement"
  let wrapped ← constant (.binary .wordAdd (.word Word.maximum) (word 1))
  let wrappedPlan ← plan wrapped identity
  for input in Modules.boundaryInputs do
    ensure (Modules.observe wrappedPlan input 10000 == returned (expected Word.zero input Word.zero))
      "original constant Word overflow was not preserved"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Modules.generatedPlan (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "module skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  -- All joint helper/template residues have a bounded, fully checked skeleton.
  for seed in List.range 36 do
    let budget ← minimumBudget seed
    ensure (budget ≤ 512) "maximum module budget cannot hold a selected template skeleton"
    let (value, _) ← get (Modules.generatedPlan (Seed.ofNat seed) budget)
    ensure (Wire.programNodes (value.instantiate Word.zero) ≤ budget &&
      value.step.helpers.length == 1 + seed % 3)
      "module generation escaped its full node or helper constraints"
    ensure (!(Modules.generatedPlan (Seed.ofNat seed) (budget - 1)).isOk &&
      !(Modules.generatedPlan (Seed.ofNat seed) 513).isOk) "module node bounds were not enforced"
  let corpus := Modules.generateCases (Seed.ofNat 0) 384 8 512 10000
  ensure (corpus == Modules.generateCases (Seed.ofNat 0) 384 8 512 10000)
    "module generation is nondeterministic"
  let rows ← cases corpus
  ensure (rows.size == 8 && (← natural corpus "attempted") ≤ 512)
    "bounded module generation did not complete"
  for (row, index) in rows.toList.zipIdx do
    let admitted ← get (Modules.caseProgram row)
    ensure (Wire.programNodes admitted.program ≤ 384 &&
      some admitted.input == Modules.boundaryInputs[index % 4]?) "module generation changed boundary order/budget"
    ensure ((← get (Modules.replayCase row 10000)) == row) "generated module provenance did not replay"
    let low ← get (Modules.replayCase row 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "fresh module observation fuel changed saved validation fuel"
  let saved := rows[3]!
  let origin ← field (← field saved "provenance") "origin"
  let seedText ← string origin "seed"
  let some seed := seedText.toNat? | throw (IO.userError "invalid generated seed")
  let low := Modules.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource")
    "module generation fuel exhaustion was classified as a semantic exclusion"
  ensure ((← cases (Modules.generateCases (Seed.ofNat seed) 384 3 1 10000)).size == 3 &&
    (← string (Modules.generateCases (Seed.ofNat seed) 384 5 1 10000) "status") == "generation-exhausted")
    "module count/attempt limits did not distinguish cases from function candidates"
  ensure ((← natural (Modules.generateCases (Seed.ofNat seed) 384 0 100 10000) "attempted") == 0 &&
    (← cases (Modules.generateCases (Seed.ofNat seed) 384 1 0 10000)).isEmpty)
    "empty module generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Modules.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 10000) "tampered module version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "forged"),
      ("maxProgramNodes", toJson (513 : Nat)),
      ("stepOrigin", Json.null), ("constantOrigin", Json.null), ("inputIndex", toJson (4 : Nat)),
      ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! name value)) 10000)
      s!"tampered module {name} accepted"
  let stepOrigin ← field origin "stepOrigin"
  for name in ["seed", "finalSeed", "maxProgramNodes", "helpers", "helperCount"] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! "stepOrigin"
      (stepOrigin.setObjVal! name Json.null))) 10000) "tampered nested step recipe accepted"
  let constantOrigin ← field origin "constantOrigin"
  for name in ["kind", "seed", "finalSeed", "maxProgramNodes"] do
    rejected (Modules.replayCase (withOrigin (origin.setObjVal! "constantOrigin"
      (constantOrigin.setObjVal! name Json.null))) 10000) "tampered constant recipe accepted"
  rejected (Modules.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "constantFeatures" (toJson ([] : List String)))) 10000)
    "tampered constant feature provenance accepted"
  let admitted ← get (Modules.caseProgram saved)
  let wrongProgram := Wire.encodeProgram (admitted.plan.step.instantiate admitted.input)
  for kind in ["imported", "reduced", "module-generated"] do
    let changed := (withOrigin (origin.setObjVal! "kind" (toJson kind))).setObjVal! "program" wrongProgram
    rejected (Modules.caseProgram changed) "noncanonical program accepted under a different origin"
    rejected (Modules.replayCase changed 10000) "replay skipped canonical comparison for an origin"
  let modulePlan ← field saved "modulePlan"
  let changedConstant ← constant (word 17)
  rejected (Modules.caseProgram (saved.setObjVal! "modulePlan"
    (modulePlan.setObjVal! "constantProgram" (Wire.encodeProgram changedConstant.program))))
    "changed constant program was not compared against the full original reference"
  let free : Wire.Program := {resultType := .word, dataDefinitions := [], body := .var 0}
  rejected (Modules.checkedPlan (modulePlan.setObjVal! "constantProgram" (Wire.encodeProgram free)))
    "constant captured an outer runtime input"
  for (name, value) in [("variant", toJson "offset"), ("schema", toJson "unknown"),
      ("unexpected", toJson true)] do
    rejected (Modules.checkedPlan (modulePlan.setObjVal! name value)) "malformed module plan accepted"
  rejected (Modules.caseProgram (saved.setObjVal! "input" (toJson "01"))) "noncanonical module input accepted"
  rejected (Modules.caseProgram (saved.setObjVal! "input" (toJson "0"))) "input/reference mismatch accepted"
  rejected (Modules.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale module source accepted"
  let bundle ← field saved "sourceBundle"
  let files ← get (bundle.getObjValAs? (Array Json) "files")
  let changedBundle := fun changed => saved.setObjVal! "sourceBundle" changed
  for changed in [bundle.setObjVal! "entry" (toJson "common.sol"),
      bundle.setObjVal! "extra" (toJson true),
      bundle.setObjVal! "files" (.arr (files.extract 0 3)),
      bundle.setObjVal! "files" (.arr (files.push files[0]!)),
      bundle.setObjVal! "files" (toJson files.toList.reverse)] do
    rejected (Modules.replayCase (changedBundle changed) 10000)
      "missing/extra/reordered module bundle accepted"
  for index in List.range files.size do
    let file := files[index]!
    let text ← string file "source"
    let changed := files.set! index (file.setObjVal! "source" (toJson (text ++ "\n")))
    rejected (Modules.replayCase (changedBundle (bundle.setObjVal! "files" (.arr changed))) 10000)
      "changed source dependency was ignored"
  for path in ["../common.sol", "/tmp/common.sol", "case.sol", "common.txt"] do
    let changed := files.set! 1 (files[1]!.setObjVal! "path" (toJson path))
    rejected (Modules.replayCase (changedBundle (bundle.setObjVal! "files" (.arr changed))) 10000)
      "noncanonical dependency path accepted"

  let contract ← field saved "contract"
  rejected (Modules.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 10000)
    "wrong module ABI input accepted"

private def shrinkChecks : IO Unit := do
  let graph ← checked [Aggregate.template 3 (word 2)]
  let fixed ← constant constantBody
  let value ← plan fixed graph
  let saved ← imported value Word.maximum
  let original ← get (Modules.caseProgram saved)
  let shrunk ← get (Modules.shrinkCases saved 1000 10000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Modules.shrinkCases saved 1000 10000)))
    "module shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut stepReduced := false
  let mut constantReduced := false
  for row in rows do
    let candidate ← get (Modules.caseProgram row)
    ensure (candidate.program.check && candidate.plan.step.helpers.length == graph.helpers.length &&
      Aggregate.bindingInventory candidate.plan.step == Aggregate.bindingInventory graph)
      "module reduction lost a step binder/helper or changed its composition"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "module reduction did not decrease the full original Core program"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "module reduction duplicated a canonical program"
    seen := key :: seen
    ensure ((← get (Modules.replayCase row 10000)) == row) "module reduction did not replay"
    inputReduced := inputReduced || candidate.input != original.input
    constantReduced := constantReduced || Wire.encodeProgram candidate.plan.constant.program != Wire.encodeProgram fixed.program
    stepReduced := stepReduced || Wire.encodeProgram candidate.plan.step.program != Wire.encodeProgram graph.program
  ensure (inputReduced && stepReduced && constantReduced) "module reduction omitted constant, input or step candidates"
  ensure ((← cases (← get (Modules.shrinkCases saved 2 10000))) == rows.extract 0 2 &&
    (← cases (← get (Modules.shrinkCases saved 0 10000))).isEmpty) "module shrink limit changed ordering"
  let reduced := rows[0]!
  let candidate ← get (Modules.caseProgram reduced)
  let provenance ← field reduced "provenance"
  let origin ← field provenance "origin"
  for (name, value) in [("parentProgram", Wire.encodeProgram candidate.program),
      ("parentInput", toJson "00"), ("extra", toJson true)] do
    rejected (Modules.replayCase (reduced.setObjVal! "provenance"
      (provenance.setObjVal! "origin" (origin.setObjVal! name value))) 10000)
      "tampered reduction witness accepted"
  let sameParent := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", Wire.encodeProgram candidate.program), ("parentPlan", Modules.planJson candidate.plan),
    ("parentInput", toJson (toString candidate.input.val))]
  rejected (Modules.replayCase (reduced.setObjVal! "provenance"
    (provenance.setObjVal! "origin" sameParent)) 10000) "non-strict reduction origin accepted"


def testSourceModuleCases : IO Unit := do
  referenceChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceModuleCases
end

section
-- leanmerge: from Solcore.Test.SourceModuleEmitter
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
    ensure (file.source.startsWith "pragma solcore;\nimport * from std;\n" && file.source.endsWith "\n")
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
    Solcore.Synthesis.Source.Modules.emitterVersion == "solcore-source-modules-v3" &&
    Solcore.Synthesis.Source.Modules.wrapperVersion == "solcore-word-modules-contract-v1")
    "module provenance or contract metadata changed"

def testSourceModuleEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceModuleEmitter
end

section
-- leanmerge: from Solcore.Test.SourceMutationEmitter
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
  "pragma solcore;", "import * from std;", "import * from std.dispatch;", "",
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
  ensure (Mutation.emitterVersion == "solcore-source-mutation-v2" &&
    Mutation.wrapperVersion == "solcore-word-mutation-contract-v1" &&
    Mutation.selector == "0xa444f5e9" && LocalMutation.version == "core-local-mutation-dag-v1")
    "mutation provenance changed"

def testSourceMutationEmitter : IO Unit := do
  admissionChecks
  executionChecks
  formattingChecks

end Tests.SourceMutationEmitter
end

section
-- leanmerge: from Solcore.Test.SourceMutationCases
/-! Case-level mutation replay and reduction checks. Concrete index goldens
cover reads before writes, Unit binders, two cells and private helper cells. -/
set_option autoImplicit false

namespace Tests.SourceMutationCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.LocalMutation (CheckedDAG)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)
private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def checked (helpers : List Wire.Expr) (body : Wire.Expr := entry) : IO CheckedDAG :=
  match CheckedDAG.ofParts? helpers body with
  | some graph => pure graph
  | none => throw (IO.userError "mutation case fixture failed checked admission")
private def imported (graph : CheckedDAG) (input : Word) : IO Json :=
  get (Mutation.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 3000)
private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def templateResult (pattern count : Nat) (input : Word) : Word :=
  let constant := Word.ofNatModulo 2
  if pattern = 0 then input.add (Word.ofNatModulo (2 * count))
  else if pattern = 1 then
    (List.range count).foldl (fun value _ =>
      if value.val > 2 then value.add constant else value.sub constant) input
  else if pattern = 2 then
    let pair := (List.range count).foldl (fun (pair : Word × Word) index =>
      if index % 2 = 0 then (pair.1.add pair.2 |>.add constant, pair.2)
      else (pair.1, pair.2.add pair.1 |>.add constant)) (input, input)
    pair.1.add pair.2
  else input.add (Word.ofNatModulo (2 + count - 1))

private def indexChecks : IO Unit := do
  for pattern in List.range 4 do
    for count in [1, 2, 3, 4] do
      let graph ← checked [Mutation.template pattern count (word 2)]
      ensure ((Mutation.bindingInventory graph).count .unit == count)
        "template did not retain all update Unit binders"
      ensure (graph.features.count "newCell" == if pattern = 2 then 2 else 1)
        "template allocated the wrong number of private cells"
      for input in Input.boundaryInputs do
        ensure (Mutation.observe graph input 3000 == returned (templateResult pattern count input))
          s!"template index mismatch: pattern {pattern}, count {count}, input {input.val}"
  let snapshot ← checked [SourceMutationEmitter.snapshotBody]
  ensure (Mutation.observe snapshot (Word.ofNatModulo 1) 3000 == returned (Word.ofNatModulo 3))
    "load-before-store returned the overwritten value instead of the original snapshot"
  for (_, helpers, body) in SourceMutationEmitter.fixtures do
    let graph ← checked helpers body
    let mut source : Option String := none
    for input in Input.boundaryInputs do
      let saved ← imported graph input
      let current ← string saved "source"
      if let some previous := source then ensure (previous == current) "mutation source depends on input"
      source := some current
      let admitted ← get (Mutation.caseProgram saved)
      ensure (admitted.program.check && admitted.input == input) "mutation case changed its original Core"
      ensure ((← get (Mutation.replayCase saved 3000)) == saved) "imported mutation case did not replay"
      ensure ((← get (Mutation.replayCase (saved.setObjVal! "directCore" (returned Word.zero)) 3000)) == saved)
        "mutation replay trusted a saved result"
      let low ← get (Mutation.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "zero fuel was confused with mutation completion"

private def minimumBudget (seed : Nat) : IO Nat := do
  for nodes in List.range 513 do
    if (Mutation.generatedFunction (Seed.ofNat seed) nodes).isOk then return nodes
  throw (IO.userError "mutation skeleton did not fit the case node limit")

private def generationChecks : IO Json := do
  let mut saved := Json.null
  for seed in List.range 3 do
    let budget ← minimumBudget seed
    let corpus := Mutation.generateCases (Seed.ofNat seed) budget 4 1 3000
    ensure (corpus == Mutation.generateCases (Seed.ofNat seed) budget 4 1 3000)
      "mutation generation is nondeterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimal measured skeleton did not generate one four-input case group"
    let rows ← cases corpus
    ensure (rows.size == 4) "generated mutation group omitted boundary inputs"
    for index in List.range 4 do
      let row := rows[index]!
      let graph ← get (Mutation.caseProgram row)
      ensure (graph.program.check && graph.function.helpers.length == seed + 1 &&
        Wire.programNodes graph.program ≤ budget) "mutation generation escaped helper/type/node budget"
      ensure (some graph.input == Input.boundaryInputs[index]?) "mutation boundary input order changed"
      ensure ((← get (Mutation.replayCase row 3000)) == row) "generated mutation provenance did not replay"
      let low ← get (Mutation.replayCase row 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "fresh replay fuel changed original validation fuel"
      saved := row
    ensure ((← cases (Mutation.generateCases (Seed.ofNat seed) (budget - 1) 1 1 3000)).isEmpty)
      "insufficient skeleton budget silently changed the selected template"
  let corpus := Mutation.generateCases (Seed.ofNat 0) 192 8 256 3000
  ensure ((← cases corpus).size == 8 && (← natural corpus "attempted") ≤ 256)
    "bounded mixed mutation corpus did not complete"
  for row in ← cases corpus do
    let graph ← get (Mutation.caseProgram row)
    ensure (Wire.programNodes graph.program ≤ 192) "closed G0 embedding exceeded the full program budget"
    ensure ((← get (Mutation.replayCase row 3000)) == row) "mixed mutation metadata failed replay"
  let budget ← minimumBudget 0
  let low := Mutation.generateCases (Seed.ofNat 0) budget 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource") "generation fuel was a semantic exclusion"
  ensure ((← cases (Mutation.generateCases (Seed.ofNat 0) budget 3 1 3000)).size == 3)
    "case count did not truncate a boundary group"
  ensure ((← string (Mutation.generateCases (Seed.ofNat 0) budget 5 1 3000) "status") == "generation-exhausted")
    "mutation attempt limit counted inputs instead of function candidates"
  ensure ((← natural (Mutation.generateCases (Seed.ofNat 0) 192 0 100 3000) "attempted") == 0 &&
    (← cases (Mutation.generateCases (Seed.ofNat 0) 192 1 0 3000)).isEmpty)
    "empty generation budgets consumed work"
  return saved

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for version in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Mutation.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 3000) "tampered mutation version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helpers", Json.arr #[]),
      ("helperCount", toJson (0 : Nat)), ("inputIndex", toJson (10 : Nat)),
      ("validationFuel", toJson (10000001 : Nat))] do
    rejected (Mutation.replayCase (withOrigin (origin.setObjVal! name value)) 3000)
      s!"tampered mutation {name} accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  for name in ["seed", "finalSeed", "maxProgramNodes", "template", "updates"] do
    let changed := metadata[0]!.setObjVal! name (toJson "forged")
    rejected (Mutation.replayCase (withOrigin (origin.setObjVal! "helpers" (.arr (metadata.set! 0 changed)))) 3000)
      "tampered helper template metadata accepted"
  rejected (Mutation.replayCase (saved.setObjVal! "source" (toJson "stale")) 3000) "stale mutation source accepted"
  rejected (Mutation.replayCase (saved.setObjVal! "input" (toJson "0")) 3000) "input/application mismatch accepted"
  let contract ← field saved "contract"
  rejected (Mutation.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "calldata" (toJson "0x"))) 3000)
    "wrong mutation ABI input accepted"
  let bad : Wire.Expr := .letE (.newCell .word (.var 0)) (.letE .unit (.loadCell (.var 0)))
  rejected (Mutation.checkedFunction (Wire.encodeProgram (functionDAGProgram [bad] entry)))
    "eliding a Unit binder changed the referenced cell without rejection"

private def shrinkChecks : IO Unit := do
  for body in [SourceMutationEmitter.snapshotBody, SourceMutationEmitter.boolAndUnitBody,
      SourceMutationEmitter.nestedStoreBody] do
    let graph ← checked [body]
    let saved ← imported graph Word.maximum
    let original ← get (Mutation.caseProgram saved)
    let shrunk ← get (Mutation.shrinkCases saved 1000 3000)
    let rows ← cases shrunk
    ensure (!rows.isEmpty && shrunk == (← get (Mutation.shrinkCases saved 1000 3000)))
      "mutation shrinking was empty or nondeterministic"
    let mut seen : List String := []
    let mut inputReduced := false
    let mut storesReduced := false
    for row in rows do
      let candidate ← get (Mutation.caseProgram row)
      ensure (candidate.program.check && candidate.function.helpers.length == graph.helpers.length &&
        Mutation.bindingInventory candidate.function == Mutation.bindingInventory graph &&
        candidate.function.features.count "newCell" == graph.features.count "newCell")
        "shrink erased/retyped a cell, Unit or scalar binder"
      ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
        "mutation reduction did not strictly decrease the original Core program"
      let key := (Wire.encodeProgram candidate.program).compress
      ensure (!seen.contains key) "mutation reduction duplicated a candidate"
      seen := key :: seen
      ensure ((← get (Mutation.replayCase row 3000)) == row) "mutation reduction did not replay"
      inputReduced := inputReduced || candidate.input != original.input
      storesReduced := storesReduced || candidate.function.features.count "storeCell" < graph.features.count "storeCell"
    ensure (inputReduced && storesReduced) "mutation shrinking omitted input or store-to-Unit candidates"
    ensure ((← cases (← get (Mutation.shrinkCases saved 2 3000))) == rows.extract 0 2 &&
      (← cases (← get (Mutation.shrinkCases saved 0 3000))).isEmpty) "mutation shrink limit changed ordering"

def testSourceMutationCases : IO Unit := do
  indexChecks
  let saved ← generationChecks
  tamperingChecks saved
  shrinkChecks

end Tests.SourceMutationCases
end

section
-- leanmerge: from Solcore.Test.SourcePrimitiveCases
/-! Runtime-input generation, original-Core observation, strict replay and
closed-lambda shrinking. Compiler agreement is checked separately by the real
Rust/Core/EVM integration runner. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejected {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def function (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some checked => pure checked
  | none => throw (IO.userError "input-case fixture did not typecheck")

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def field (value : Json) (key : String) : IO Json := get (value.getObjVal? key)
private def string (value : Json) (key : String) : IO String := get (value.getObjValAs? String key)
private def natural (value : Json) (key : String) : IO Nat := get (value.getObjValAs? Nat key)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")

private def imported (body : Wire.Expr) (input : Word) : IO Json := do
  get (Primitive.emitCase (← function body) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def primitiveChecks : IO Unit := do
  ensure (Primitive.appliedOverhead == 5 && Primitive.minimumProgramNodes == 8)
    "complete applied node overhead changed"
  ensure (Primitive.boundaryInputs.map (·.val) ==
    [0, 1, 2, 255, 256, Word.maximum.val, 2 ^ 255, 2 ^ 255 - 1])
    "primitive boundary bank changed"
  let maximum := Word.maximum.val
  let high := 2 ^ 255
  -- Independent small goldens exercise the actual Core evaluator; source never
  -- supplies expected results. Every saved edge case must also replay canonically.
  let fixtures : List (Wire.Expr × Nat × Nat) := [
    (.binary .wordDiv (.var 0) (word 0), maximum, 0),
    (.binary .wordMod (.var 0) (word 0), high, 0),
    (.binary .wordSdiv (.var 0) (word maximum), high, high),
    (.binary .wordSdiv (.var 0) (word 2), maximum - 6, maximum - 2),
    (.binary .wordSmod (.var 0) (word 2), maximum - 6, maximum),
    (.ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0), high, 0),
    (.ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0), high - 1, 1),
    (.binary .wordShl (word 1) (.var 0), 0, 1),
    (.binary .wordShl (word 1) (.var 0), 255, high),
    (.binary .wordShl (word 1) (.var 0), 256, 0),
    (.binary .wordShl (word 1) (.var 0), maximum, 0),
    (.binary .wordShr (word maximum) (.var 0), 0, maximum),
    (.binary .wordShr (word maximum) (.var 0), 255, 1),
    (.binary .wordShr (word maximum) (.var 0), 256, 0),
    (.binary .wordSar (word high) (.var 0), maximum, maximum),
    (.ternary .wordAddMod (.var 0) (word 1) (word maximum), maximum, 1),
    (.ternary .wordMulMod (.var 0) (word 2) (word maximum), high, 1),
    (.ternary .wordAddMod (.var 0) (word maximum) (word 0), maximum, 0),
    (.ternary .wordMulMod (.var 0) (word maximum) (word 0), maximum, 0),
    (.unary .wordClz (.var 0), 0, 256),
    (.unary .wordClz (.var 0), maximum, 0),
    (.unary .wordClz (.var 0), high, 0),
    (.unary .wordClz (.var 0), 1, 255),
    (.binary .wordByte (.var 0) (word 0x1234), 31, 0x34),
    (.binary .wordByte (.var 0) (word maximum), 32, 0),
    (.binary .wordByte (.var 0) (word maximum), maximum, 0),
    (.binary .wordSignExtend (word 0) (.var 0), 0x7f, 0x7f),
    (.binary .wordSignExtend (word 0) (.var 0), 0x80, maximum - 0x7f),
    (.binary .wordSignExtend (.var 0) (word high), 31, high),
    (.binary .wordSignExtend (.var 0) (word high), 32, high),
    (.binary .wordPow (.var 0) (word 0), 0, 1),
    (.binary .wordPow (.var 0) (word 0), maximum, 1),
    (.binary .wordPow (word 2) (.var 0), maximum, 0),
    (.binary .wordPow (word maximum) (.var 0), maximum, maximum)]
  for (body, input, expected) in fixtures do
    let saved ← imported body (Word.ofNatModulo input)
    ensure ((← field saved "directCore") == returned (Word.ofNatModulo expected))
      s!"primitive Core boundary differs at input {input}: {reprStr body}"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "primitive boundary replay differs"
    ensure (← get (Primitive.caseProgram saved)).program.check "primitive boundary escaped Core typing"
  -- A scoped ternary branch uses both the let binder and original parameter.
  let nestedBody : Wire.Expr := .letE (.binary .wordAdd (.var 0) (word 1))
    (.ifE (.binary .wordSgt (.var 1) (word 0))
      (.ternary .wordAddMod (.var 0) (.var 1) (word 7))
      (.binary .wordByte (word 31) (.var 0)))
  for (input, expected) in [(0, 1), (1, 3), (maximum, 0), (high, 1)] do
    let saved ← imported nestedBody (Word.ofNatModulo input)
    ensure ((← field saved "directCore") == returned (Word.ofNatModulo expected))
      "scoped primitive let/branch altered binder meanings"
    let reductions ← get (Primitive.shrinkCases saved 20 1000)
    for row in (← cases reductions) do
      let _ ← get (Primitive.replayCase row 1000)
      ensure (← get (Primitive.caseProgram row)).program.check "primitive shrink escaped Core typing"

private def inputChecks : IO Unit := do
  for input in Primitive.boundaryInputs do
    ensure ((← get (Primitive.inputWord (toString input.val))) == input) "boundary input round trip failed"
    let encoded := Primitive.calldata input
    ensure (encoded.length == 74 && encoded.startsWith Primitive.selector) "ABI input width/selector changed"
  ensure (Primitive.calldata Word.zero == "0xa444f5e9" ++ String.ofList (List.replicate 64 '0'))
    "zero input ABI encoding changed"
  ensure (Primitive.calldata Word.maximum == "0xa444f5e9" ++ String.ofList (List.replicate 64 'f'))
    "maximum input ABI encoding changed"
  ensure (Primitive.calldata (Word.ofNatModulo (2 ^ 255)) ==
    "0xa444f5e98" ++ String.ofList (List.replicate 63 '0')) "high-bit input ABI encoding changed"
  for invalid in ["", "00", "01", "-1", "+1", "0x1", " 1", toString (2 ^ 256 : Nat)] do
    rejected (Primitive.inputWord invalid) "noncanonical or overflowing input accepted"
  let identity ← function (.var 0)
  let mut source : Option String := none
  for input in Primitive.boundaryInputs do
    let saved ← get (Primitive.emitCase identity input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let emittedSource ← string saved "source"
    if let some prior := source then
      ensure (prior == emittedSource) "source text depends on runtime input"
    source := some emittedSource
    let checked ← get (Primitive.caseProgram saved)
    ensure (checked.program.check && checked.input == input) "applied original Core did not typecheck"
    ensure ((← field saved "directCore") == returned input) "identity did not use its runtime input"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "imported case did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 17))
    ensure ((← get (Primitive.replayCase forged 1000)) == saved) "saved expected result was trusted"
    let exhausted ← get (Primitive.replayCase saved 0)
    ensure ((← string (← field exhausted "directCore") "status") == "out-of-fuel")
      "zero fuel was treated as a completed observation"
  let branch ← function (.ifE (.binary .wordGt (.var 0) (word 1)) (word 7) (word 0))
  ensure (Primitive.observe branch Word.zero 1000 == Primitive.observe branch (Word.ofNatModulo 1) 1000)
    "branch fixture should agree on zero and one"
  let _ ← get (Primitive.inputSensitive branch 1000)
  rejected (Primitive.inputSensitive (← function (word 7)) 1000) "constant generation candidate accepted"
  rejected (Primitive.inputSensitive identity 0) "fuel exhaustion passed the dynamic-input filter"
  let constant ← imported (word 7) Word.maximum
  ensure ((← field constant "directCore") == returned (Word.ofNatModulo 7))
    "imported constant functions must remain valid for shrinking"
  let oversized := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  rejected (Primitive.emitCase (← function oversized) Word.zero
    (Json.mkObj [("kind", toJson "imported")]) 1000) "oversized applied function escaped case limit"

private def generationChecks : IO Json := do
  let corpus := Primitive.generateCases (Seed.ofNat 0) 24 17 64 1000
  ensure (corpus == Primitive.generateCases (Seed.ofNat 0) 24 17 64 1000)
    "input generation is nondeterministic"
  ensure ((← string corpus "status") == "complete") "bounded input corpus did not complete"
  let rows ← cases corpus
  let attempted ← natural corpus "attempted"
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  ensure (rows.size == 17 && attempted ≤ 64 && attempted == 3 + excluded.size)
    "function attempts and individual case counts were confused"
  for index in List.range rows.size do
    let saved := rows[index]!
    let checked ← get (Primitive.caseProgram saved)
    let provenance ← field saved "provenance"
    let origin ← field provenance "origin"
    ensure ((← natural origin "inputIndex") == index % 8 &&
      some checked.input == Primitive.boundaryInputs[index % 8]?) "boundary order changed"
    ensure ((← string provenance "profileVersion") == Primitive.profileVersion &&
      (← string provenance "generatorVersion") == Primitive.generatorVersion &&
      (← string provenance "baseGeneratorVersion") == generatorVersion &&
      (← string provenance "boundaryVersion") == Primitive.boundaryVersion) "profile version changed G0"
    ensure (checked.program.check && Wire.programNodes checked.program ≤ 24)
      "generated applied case escaped checker/node bound"
    ensure ((← get (Primitive.replayCase saved 1000)) == saved) "generated input replay differs"
    let suspended ← get (Primitive.replayCase saved 0)
    ensure ((← string (← field suspended "directCore") "status") == "out-of-fuel")
      "generated replay confused its new observation budget with its validation budget"
    if index % 8 != 0 then
      ensure ((← string saved "source") == (← string rows[index - index % 8]! "source"))
        "one function's boundary cases emitted different source"
  let truncated := Primitive.generateCases (Seed.ofNat 0) 8 3 1 1000
  ensure ((← cases truncated).size == 3 && (← natural truncated "attempted") == 1 &&
    (← string truncated "status") == "complete") "case count did not truncate the input group"
  let exhausted := Primitive.generateCases (Seed.ofNat 0) 8 9 1 1000
  ensure ((← cases exhausted).size == 8 && (← string exhausted "status") == "generation-exhausted")
    "attempt limit counted input cases instead of functions"
  for corpus in [Primitive.generateCases (Seed.ofNat 0) 7 1 3 1000,
      Primitive.generateCases (Seed.ofNat 0) 8 1 3 0] do
    ensure ((← cases corpus).isEmpty && (← natural corpus "attempted") == 3 &&
      (← string corpus "status") == "generation-exhausted") "failed generation lost its bound"
    ensure ((← get (corpus.getObjValAs? (Array Json) "excluded")).size == 3)
      "generation failures were not recorded"
  ensure ((← natural (Primitive.generateCases (Seed.ofNat 0) 8 0 100 1000) "attempted") == 0)
    "zero case request consumed attempts"
  ensure ((← cases (Primitive.generateCases (Seed.ofNat 0) 8 1 0 1000)).isEmpty)
    "zero attempt limit ignored"
  let resources ← get ((Primitive.generateCases (Seed.ofNat 0) 8 1 1 0).getObjValAs? (Array Json) "excluded")
  ensure ((← string resources[0]! "category") == "inconclusive-resource" &&
    (← string resources[0]! "code") == "boundary-out-of-fuel")
    "generation fuel exhaustion lost its resource classification"
  for budget in [8, 96, 512] do
    let bounded := Primitive.generateCases (Seed.ofNat 0) budget 8 64 1000
    ensure ((← string bounded "status") == "complete") "supported budget did not yield a function"
    for row in (← cases bounded) do
      let admitted ← get (Primitive.caseProgram row)
      ensure (Wire.programNodes admitted.program ≤ budget)
        "generator counted only its scalar body instead of the applied function"
      let _ ← get (Primitive.replayCase row 1000)
  let invalid := Primitive.generateCases (Seed.ofNat 0) 513 1 1 1000
  ensure ((← cases invalid).isEmpty && (← natural invalid "attempted") == 1)
    "oversized generation request accepted"
  return corpus

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved := (← cases corpus)[0]!
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["profileVersion", "functionVersion", "abstractionVersion",
      "generatorVersion", "baseGeneratorVersion", "boundaryVersion", "emitterVersion", "wrapperVersion"] do
    rejected (Primitive.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "00"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (999 : Nat)), ("inputIndex", toJson (9 : Nat)),
      ("maxProgramNodes", toJson (513 : Nat)), ("baseProgramNodes", toJson (512 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("kind", toJson "unknown")] do
    rejected (Primitive.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "input" (toJson "1")) 1000)
    "input/program disagreement accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "source" (toJson "forged")) 1000)
    "stale source accepted"
  let contract ← field saved "contract"
  for (name, value) in [("calldata", toJson "0xa444f5e9"),
      ("signature", toJson "run()"), ("runtimePath", toJson ["Other"])] do
    rejected (Primitive.replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "tampered ABI metadata accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000) "tampered features accepted"
  let identity ← function (.var 0)
  let badProgram := Wire.encodeProgram identity.program
  rejected (Primitive.caseProgram (saved.setObjVal! "program" badProgram))
    "bare lambda accepted as an applied input case"
  let invalidFunction : Wire.Program := {
    resultType := .function .word .word, dataDefinitions := [], body := .lambda .word .word (.var 1) }
  rejected (Primitive.checkedFunction (Wire.encodeProgram invalidFunction)) "unbound parameter escaped sealing"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "unexpected" (toJson true))) 1000)
    "extra generated provenance accepted"
  rejected (Primitive.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "unexpected" (toJson true))) 1000) "extra profile provenance accepted"
  let constant ← imported (word 7) Word.zero
  let constantProvenance ← field constant "provenance"
  rejected (Primitive.replayCase (constant.setObjVal! "provenance"
    (constantProvenance.setObjVal! "origin" (Json.mkObj [
      ("kind", toJson "imported"), ("seed", toJson "0")]))) 1000)
    "extra imported provenance accepted"
  let generated ← get ((generate {
    seed := Seed.ofNat 0,
    maxProgramNodes := 24 - Primitive.appliedOverhead}).mapError reprStr)
  let some constantFunction := CheckedWordFunction.fromProgram? generated.checkedProgram 0 |
    throw (IO.userError "constant generation fixture changed")
  let forgedOrigin := Json.mkObj [("kind", toJson "primitive-generated"),
    ("seed", toJson "0"), ("finalSeed", toJson (toString generated.finalSeed.toNat)),
    ("maxProgramNodes", toJson (24 : Nat)), ("baseProgramNodes", toJson generated.maxProgramNodes),
    ("literalIndex", toJson (0 : Nat)), ("inputIndex", toJson (0 : Nat)),
    ("validationFuel", toJson (1000 : Nat))]
  let forged ← get (Primitive.emitCase constantFunction Word.zero forgedOrigin 1000)
  rejected (Primitive.replayCase forged 1000)
    "replay skipped the generated boundary variation requirement"

private def shrinkChecks : IO Unit := do
  let body := Wire.Expr.letE (.binary .wordAdd (.var 0) (word 17))
    (.ifE (.binary .wordGt (.var 0) (word 1))
      (.binary .wordXor (.var 0) (.var 1)) (word 99))
  let saved ← imported body Word.maximum
  let source ← get (Primitive.caseProgram saved)
  let shrunk ← get (Primitive.shrinkCases saved 100 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Primitive.shrinkCases saved 100 1000)))
    "input shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut changedInput := false
  let mut changedBody := false
  let mut constant := false
  for row in rows do
    let reduced ← get (Primitive.caseProgram row)
    ensure (reduced.program.check && Wire.programNodes reduced.program ≤ 512)
      "shrink escaped the applied lambda/checker/size boundary"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity source.program.body))
      "input reduction was not strictly smaller"
    let key := (Wire.encodeProgram reduced.program).compress
    ensure (!seen.contains key) "input shrink produced duplicate programs"
    seen := key :: seen
    ensure ((← get (Primitive.replayCase row 1000)) == row) "shrunk input did not replay"
    let emitted ← get ((Primitive.emit reduced.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "shrink retained stale emitted source"
    changedInput := changedInput || reduced.input != source.input
    changedBody := changedBody || Wire.encodeExpr reduced.function.body != Wire.encodeExpr source.function.body
    constant := constant || Wire.encodeExpr reduced.function.body == Wire.encodeExpr (word 0)
  ensure (changedInput && changedBody && constant) "shrinking missed input/body/constant candidates"
  ensure ((← cases (← get (Primitive.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "input shrink limit changed ordering"
  ensure ((← cases (← get (Primitive.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Primitive.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 100 1000)
    "shrinker accepted a stale source case"
  let row := rows[0]!
  let provenance ← field row "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun value => row.setObjVal! "provenance" (provenance.setObjVal! "origin" value)
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "parentProgram"
    (← field row "program"))) 1000) "nonstrict or input-mismatched parent accepted"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "parentInput" (toJson "00"))) 1000)
    "noncanonical parent input accepted"
  rejected (Primitive.replayCase (withOrigin (origin.setObjVal! "unexpected" (toJson true))) 1000)
    "extra reduced provenance accepted"
  let selfOrigin := Json.mkObj [("kind", toJson "reduced"),
    ("parentProgram", ← field row "program"), ("parentInput", ← field row "input")]
  rejected (Primitive.replayCase (withOrigin selfOrigin) 1000) "self-parent reduction accepted"


def testSourcePrimitiveCases : IO Unit := do
  primitiveChecks
  inputChecks
  let corpus ← generationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourcePrimitiveCases
end

section
-- leanmerge: from Solcore.Test.SourcePrimitiveCorpus
/-! Validate the committed primitive corpus against actual checked Core
execution. Expected Words are fixed boundary goldens, never compiler output.
This module does not compile Rust or execute an EVM. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveCorpus

open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let entries ← value.getObjValAs? (List String) key
  require (entries.eraseDups == entries) (key ++ " contains duplicates")
  return entries

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("profileVersion", Primitive.profileVersion), ("functionVersion", wordFunctionVersion),
  ("abstractionVersion", abstractionVersion), ("generatorVersion", Primitive.generatorVersion),
  ("baseGeneratorVersion", Solcore.Synthesis.Core.generatorVersion), ("boundaryVersion", Primitive.boundaryVersion),
  ("emitterVersion", Primitive.emitterVersion), ("wrapperVersion", Primitive.wrapperVersion)]

/-- Materialize and replay every original function application in one bounded
Core run, before any shared case-tool executable needs to be rebuilt. -/
def validateManifest (manifest : Json) (fuel : Nat := 2000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-corpus-manifest.v1" &&
    (← string manifest "profile") == "runtime-primitives" &&
    (← string manifest "coverageKind") == "core-ast-features") "unexpected primitive manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("primitive manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers requiredFeatures (Feature.catalog.toList.map featureName))
    "primitive corpus must require every scalar AST feature"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (Primitive.boundaryInputs.map fun value => toString value.val))
    "primitive corpus must require all eight boundary inputs"
  let requiredLiterals ← strings manifest "requiredWordLiterals"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 128) "primitive corpus must contain 1..128 cases"
  let mut identifiers : List String := []
  let mut inputs : List String := []
  let mut featureUnion : List String := []
  let mut literalUnion : List String := []
  let mut sources : List (String × String) := []
  let mut reductions := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifier.isEmpty && identifier.length ≤ 80 && !identifiers.contains identifier)
      "primitive case ID is empty, duplicated or too long"
    identifiers := identifiers ++ [identifier]
    let original ← entry.getObjVal? "program"
    let function ← Primitive.checkedFunction original
    require (Wire.encodeProgram function.program == original) (identifier ++ ": noncanonical function")
    let input ← Primitive.inputWord (← string entry "input")
    let expected ← Primitive.inputWord (← string entry "expectedCore")
    let expectedFeatures ← strings entry "expectedFeatures"
    let actualFeatures := (features function.body).map featureName
    require (sameMembers expectedFeatures actualFeatures && actualFeatures.contains "local")
      (identifier ++ ": expected features differ or original function lacks runtime locals")
    let origin := Json.mkObj [("kind", toJson "imported")]
    let saved ← Primitive.emitCase function input origin fuel
    require (saved == (← Primitive.emitCase function input origin fuel)) (identifier ++ ": nondeterministic emission")
    require ((← Primitive.replayCase saved fuel) == saved) (identifier ++ ": native replay differs")
    let admitted ← Primitive.caseProgram saved
    require admitted.program.check (identifier ++ ": original Core application failed its checker")
    let actual ← saved.getObjVal? "directCore"
    require ((← string actual "status") == "returned" && (← string actual "word") == toString expected.val)
      (identifier ++ ": actual Core result differs from its independent boundary golden")
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "forged")])
    require ((← Primitive.replayCase forged fuel) == saved) (identifier ++ ": stored observation became an oracle")
    let source ← string saved "source"
    let key := original.compress
    if let some (_, previous) := sources.find? (fun item => item.1 == key) then
      require (source == previous) (identifier ++ ": emitted source depends on runtime input")
    else sources := sources ++ [(key, source)]
    let candidates ← Primitive.shrinkCases saved 4 fuel
    for reduced in (← candidates.getObjValAs? (Array Json) "cases") do
      let candidate ← Primitive.caseProgram reduced
      require (candidate.program.check &&
        (complexity candidate.program.body).isStrictlySmaller (complexity admitted.program.body))
        (identifier ++ ": shrink is untyped or not strictly smaller")
      require ((← Primitive.replayCase reduced fuel) == reduced) (identifier ++ ": reduced case failed replay")
      reductions := reductions + 1
    inputs := (inputs ++ [toString input.val]).eraseDups
    featureUnion := (featureUnion ++ actualFeatures).eraseDups
    literalUnion := (literalUnion ++ (wordLiterals function.body).map (fun value => toString value.val)).eraseDups
  require (requiredFeatures.all featureUnion.contains) "native-completed cases missed required AST features"
  require (requiredInputs.all inputs.contains) "native-completed cases missed required runtime inputs"
  require (requiredLiterals.all literalUnion.contains) "native-completed cases missed required Word literals"
  return Json.mkObj [
    ("status", toJson "complete"), ("cases", toJson entries.size), ("functions", toJson sources.length),
    ("features", toJson featureUnion.length), ("inputs", toJson inputs.length), ("shrinks", toJson reductions),
    ("nativeCoreExecuted", toJson true), ("rustExecuted", toJson false), ("evmExecuted", toJson false)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid primitive corpus unexpectedly passed")

def testSourcePrimitiveCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-primitive-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first primitive case")
  let expected ← checked (Primitive.inputWord (← checked (string first "expectedCore")))
  let incorrect := first.setObjVal! "expectedCore" (toJson (toString ((expected.val + 1) % (2 ^ 256))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.set! 0 incorrect))))
  rejects (validateManifest (manifest.setObjVal! "profile" (toJson "runtime-word")))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr #[])))
  rejects (validateManifest (manifest.setObjVal! "requiredInputs" (toJson ([] : List String))))
  rejects (validateManifest (manifest.setObjVal! "requiredFeatures" (toJson ([] : List String))))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourcePrimitiveCorpus
end

section
-- leanmerge: from Solcore.Test.SourcePrimitiveEmitter
/-! Primitive printer regressions and independently executed Core boundaries.
These checks do not claim to execute Rust, EVM or emitted source. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def high : Nat := 2 ^ 255
private def maximum : Nat := Word.maximum.val

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some function => pure function
  | none => throw (IO.userError "primitive fixture failed its Core or profile check")

private def emitted (function : CheckedWordFunction) : IO EmittedProgram :=
  match Primitive.emit function with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"primitive emission failed: {reprStr error}")

private def observe (body : Wire.Expr) (input expected : Nat) : IO Unit := do
  let function ← checked body
  let program := function.instantiate (Word.ofNatModulo input)
  ensure program.check "primitive application failed Core typing"
  match program.toCore.runStateful 2000 with
  | .done (.word actual) _ =>
      ensure (actual.val == expected) s!"primitive Core result differs: got {actual.val}, expected {expected}"
  | _ => throw (IO.userError "primitive Core application did not complete")

/-- The newly supported operations, including a signed predicate used at runtime. -/
def fixtures : List (String × Wire.Expr) := [
  ("div", .binary .wordDiv (.var 0) (word 2)),
  ("mod", .binary .wordMod (.var 0) (word 2)),
  ("shl", .binary .wordShl (.var 0) (word 1)),
  ("shr", .binary .wordShr (.var 0) (word 1)),
  ("sar", .binary .wordSar (.var 0) (word 1)),
  ("sdiv", .binary .wordSdiv (.var 0) (word maximum)),
  ("smod", .binary .wordSmod (.var 0) (word 2)),
  ("sgt", .ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0)),
  ("addmod", .ternary .wordAddMod (.var 0) (word 1) (word maximum)),
  ("mulmod", .ternary .wordMulMod (.var 0) (word 2) (word maximum)),
  ("clz", .unary .wordClz (.var 0)),
  ("byte", .binary .wordByte (word 31) (.var 0)),
  ("pow", .binary .wordPow (.var 0) (word 2)),
  ("signextend", .binary .wordSignExtend (word 0) (.var 0))]

private def ordinaryChecks : IO Unit := do
  for (label, body) in fixtures do
    let function ← checked body
    ensure (PrimitiveRenderer.supported function.body) s!"supported primitive excluded: {label}"
    let source ← emitted function
    ensure (source == (← emitted function)) s!"primitive emission is not deterministic: {label}"
    ensure (source.contractName == "SynthesizedPrimitives" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedPrimitivesDeploy"] &&
      source.runtimePath == ["SynthesizedPrimitivesDeploy", "SynthesizedPrimitives"])
      "primitive wrapper metadata changed"
    let some restored := CheckedWordFunction.ofProgram? function.program |
      throw (IO.userError "primitive original failed readmission")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram function.program)
      "primitive emission changed the original Core program"
  for (label, input, expected) in [
      ("div", 0, 0), ("div", 1, 0), ("div", maximum, high - 1), ("div", high, high / 2),
      ("mod", 0, 0), ("mod", 1, 1), ("mod", maximum, 1), ("mod", high, 0),
      ("shl", 1, 2), ("shl", maximum, maximum - 1), ("shl", high, 0),
      ("shr", 1, 0), ("shr", maximum, high - 1), ("shr", high, high / 2),
      ("sar", 5, 2), ("sar", maximum, maximum), ("sar", high, high + high / 2),
      ("sdiv", 7, maximum - 6), ("sdiv", maximum, 1), ("sdiv", high, high),
      ("smod", 7, 1), ("smod", maximum - 6, maximum), ("smod", high, 0),
      ("sgt", 0, 0), ("sgt", 1, 1), ("sgt", maximum, 0), ("sgt", high, 0), ("sgt", high - 1, 1),
      ("addmod", 0, 1), ("addmod", maximum, 1), ("addmod", maximum - 1, 0),
      ("mulmod", 0, 0), ("mulmod", maximum, 0), ("mulmod", high, 1),
      ("clz", 0, 256), ("clz", 1, 255), ("clz", 2, 254),
      ("clz", maximum, 0), ("clz", high, 0), ("clz", high - 1, 1),
      ("byte", 1, 1), ("byte", maximum, 255), ("byte", high, 0),
      ("pow", 0, 0), ("pow", 1, 1), ("pow", maximum, 1), ("pow", high, 0),
      ("signextend", 127, 127), ("signextend", 128, maximum - 127),
      ("signextend", 255, maximum), ("signextend", 256, 0), ("signextend", high, 0)] do
    let some (_, body) := fixtures.find? (fun item => item.1 == label) |
      throw (IO.userError s!"missing primitive fixture {label}")
    observe body input expected

private def boundaryChecks : IO Unit := do
  for operation in [Wire.BinaryOp.wordDiv, .wordMod, .wordSdiv, .wordSmod] do
    for input in [0, 1, maximum, high] do
      observe (.binary operation (.var 0) (word 0)) input 0
  for operation in [Wire.TernaryOp.wordAddMod, .wordMulMod] do
    for input in [0, 1, maximum, high] do
      observe (.ternary operation (.var 0) (word maximum) (word 0)) input 0
      observe (.ternary operation (.var 0) (word maximum) (word 1)) input 0
  for (amount, expected) in [(0, 1), (1, 2), (255, high), (256, 0), (257, 0), (maximum, 0)] do
    observe (.binary .wordShl (word 1) (.var 0)) amount expected
  for (amount, expected) in [(0, maximum), (1, high - 1), (255, 1), (256, 0), (maximum, 0)] do
    observe (.binary .wordShr (word maximum) (.var 0)) amount expected
  for amount in [255, 256, 257, maximum] do
    observe (.binary .wordSar (word high) (.var 0)) amount maximum
    observe (.binary .wordSar (word (high - 1)) (.var 0)) amount 0
  observe (.binary .wordSdiv (.var 0) (word 2)) (maximum - 6) (maximum - 2)
  observe (.binary .wordSdiv (.var 0) (word (maximum - 1))) (maximum - 6) 3
  observe (.binary .wordSmod (.var 0) (word (maximum - 1))) (maximum - 6) maximum
  observe (.binary .wordSmod (.var 0) (word (maximum - 1))) 7 1
  observe (.binary .wordSmod (.var 0) (word maximum)) high 0
  observe (.ifE (.binary .wordSgt (.var 0) (word high)) (word 1) (word 0)) maximum 1
  observe (.ternary .wordAddMod (.var 0) (word maximum) (word (maximum - 1))) maximum 2
  observe (.ternary .wordMulMod (.var 0) (word maximum) (word (maximum - 1))) maximum 1

private def byteExponentChecks : IO Unit := do
  for (index, expected) in [(0, 128), (1, 0), (30, 18), (31, 52), (32, 0), (256, 0), (maximum, 0)] do
    observe (.binary .wordByte (.var 0) (word (high + 4660))) index expected
  for (index, expected) in [(0, maximum - 127), (1, 128), (31, 128), (32, 128), (maximum, 128)] do
    observe (.binary .wordSignExtend (.var 0) (word 128)) index expected
  observe (.binary .wordSignExtend (word 0) (.var 0)) 384 (maximum - 127)
  observe (.binary .wordSignExtend (word 1) (.var 0)) 32768 (maximum - 32767)
  for index in [31, 32, 256, maximum] do
    observe (.binary .wordSignExtend (word index) (.var 0)) high high
  for input in [0, 1, maximum, high] do
    observe (.binary .wordPow (.var 0) (word 0)) input 1
  for (base, exponent, expected) in [
      (0, 1, 0), (0, high, 0), (1, maximum, 1),
      (2, 255, high), (2, 256, 0), (2, high, 0), (2, maximum, 0),
      (maximum, maximum, maximum), (maximum, high, 1), (high, 1, high)] do
    observe (.binary .wordPow (word base) (.var 0)) exponent expected

private def legacyScalarChecks : IO Unit := do
  for (body, expected) in [
      (.unary .wordNot (.var 0), maximum - 5),
      (.ifE (.unary .boolNot (.binary .wordEq (.var 0) (word 0))) (word 1) (word 0), 1),
      (.binary .wordAdd (.var 0) (word maximum), 4),
      (.binary .wordSub (.var 0) (word 6), maximum),
      (.binary .wordMul (.var 0) (word 3), 15),
      (.binary .wordAnd (.var 0) (word 3), 1),
      (.binary .wordOr (.var 0) (word 3), 7),
      (.binary .wordXor (.var 0) (word 3), 6),
      (.ifE (.binary .wordEq (.var 0) (word 5)) (word 1) (word 0), 1),
      (.ifE (.binary .wordGt (.var 0) (word 4)) (word 1) (word 0), 1)] do
    ensure (PrimitiveRenderer.supported body) "primitive profile excluded an existing scalar operation"
    let _ ← emitted (← checked body)
    observe body 5 expected

private def renderLines (target : Target) (body : Wire.Expr) : IO (List String) :=
  match PrimitiveRenderer.render target ["sc_input"] 8 0 body with
  | .ok value => pure value.lines
  | .error error => throw (IO.userError s!"primitive formatting fixture rejected: {reprStr error}")

private def formattingChecks : IO Unit := do
  let shift : Wire.Expr := .binary .wordShl
    (.letE (word 7) (.binary .wordAdd (.var 0) (.var 1)))
    (.letE (word 1) (.var 0))
  ensure ((← renderLines .word shift) == [
    "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
    "        let sc_v2: word = (sc_v1 + sc_input);", "        let sc_v3: word = sc_v2;",
    "        let sc_v4: word = 1;", "        let sc_v5: word = sc_v4;",
    "        let sc_v6: word = sc_v5;", "        let sc_v7: word = sc_shl(sc_v6, sc_v3);"])
    "shift emission changed operand order, scope or captured argument order"
  observe shift 2 18
  ensure ((← renderLines .word (.ternary .wordAddMod (.var 0) (word 1) (word 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = 1;",
    "        let sc_v2: word = sc_v1;", "        let sc_v3: word = 0;",
    "        let sc_v4: word = sc_v3;", "        let sc_v5: word = sc_addmod(sc_v0, sc_v2, sc_v4);"])
    "modular emission did not evaluate all three original arguments in order"
  ensure ((← renderLines .bool (.binary .wordSgt (.var 0) (word 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = 0;",
    "        let sc_v2: word = sc_v1;", "        let sc_v3: bool = tobool(sc_sgt(sc_v0, sc_v2));"])
    "signed predicate did not convert the raw Word result to Bool"
  ensure ((← renderLines .word (.unary .wordClz (.var 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = sc_clz(sc_v0);"])
    "count-leading-zero emission did not preserve its operand"
  for (operation, alias) in [(Wire.BinaryOp.wordByte, "sc_byte"), (.wordSignExtend, "sc_signextend"),
      (.wordPow, "sc_exp")] do
    ensure ((← renderLines .word (.binary operation (.var 0) (word 3))) == [
      "        let sc_v0: word = sc_input;", "        let sc_v1: word = 3;",
      "        let sc_v2: word = sc_v1;", "        let sc_v3: word = " ++ alias ++ "(sc_v0, sc_v2);"])
      "index/value or base/exponent operands were reordered"
  let branch : Wire.Expr := .ifE (.bool true)
    (.letE (word 3) (.binary .wordDiv (.var 1) (.var 0)))
    (.letE (word 0) (.binary .wordMod (.var 1) (.var 0)))
  ensure ((← renderLines .word branch) == [
    "        let sc_v0: bool = true;", "        let sc_v1: word = 0;", "        if (sc_v0) {",
    "            let sc_v2: word = 3;", "            let sc_v3: word = sc_v2;",
    "            let sc_v4: word = sc_input;", "            let sc_v5: word = sc_v3;",
    "            let sc_v6: word = sc_div(sc_v4, sc_v5);", "            sc_v1 = sc_v6;", "        } else {",
    "            let sc_v7: word = 0;", "            let sc_v8: word = sc_v7;",
    "            let sc_v9: word = sc_input;", "            let sc_v10: word = sc_v8;",
    "            let sc_v11: word = sc_mod(sc_v9, sc_v10);", "            sc_v1 = sc_v11;", "        }"])
    "raw operation or local escaped its conditional branch"
  observe branch 11 3
  let identityExpected := String.intercalate "\n" [
    "pragma solcore;", "import * from std;", "import * from std.dispatch;",
    "import { div as sc_div, mod as sc_mod, shl as sc_shl, shr as sc_shr, sar as sc_sar, sdiv as sc_sdiv, smod as sc_smod, sgt as sc_sgt, addmod as sc_addmod, mulmod as sc_mulmod, clz as sc_clz, byte as sc_byte, exp as sc_exp, signextend as sc_signextend } from std.opcodes;", "",
    "contract SynthesizedPrimitives {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        return uint256(sc_input);", "    }", "}", ""]
  ensure ((← emitted (← checked (.var 0))).source == identityExpected)
    "primitive wrapper source changed its raw aliases or runtime ABI"
  ensure (Primitive.emitterVersion == "solcore-source-primitives-v2" &&
    Primitive.wrapperVersion == "solcore-word-primitives-contract-v1" && Primitive.selector == "0xa444f5e9")
    "primitive emitter version or selector changed"

private def rejectionChecks : IO Unit := do
  ensure (unaryOps.all PrimitiveRenderer.supportedUnary &&
    binaryOps.all PrimitiveRenderer.supportedBinary && ternaryOps.all PrimitiveRenderer.supportedTernary)
    "primitive profile omitted an operation from the sealed Word/Bool catalog"
  for (body, error) in [
      (.unary .integerNot (.var 0), EmitError.unsupportedUnary .integerNot),
      (.unary .integerToWord (.var 0), .unsupportedUnary .integerToWord),
      (.unary .wordToInteger (.var 0), .unsupportedUnary .wordToInteger),
      (.binary .integerDiv (.var 0) (word 0), .unsupportedBinary .integerDiv),
      (.binary .integerEq (.var 0) (word 0), .unsupportedBinary .integerEq)] do
    ensure (!(PrimitiveRenderer.supported body)) "out-of-profile operation reported supported"
    ensure (CheckedWordFunction.ofBody? body).isNone "integer operation entered the checked Word profile"
    match PrimitiveRenderer.render .word ["sc_input"] 8 0 body with
    | .error actual => ensure (actual == error) "unsupported operation gave the wrong error"
    | .ok _ => throw (IO.userError "unsupported operation was silently substituted")
  for body in [(.var 1 : Wire.Expr), .newCell .word (word 1),
      .apply (.lambda .word .word (.var 0)) (word 1), .integer 0] do
    ensure (CheckedWordFunction.ofBody? body).isNone "primitive scope admitted a host, cell or nested function"
  match PrimitiveRenderer.render .word [] 0 0 (.var 0) with
  | .error (.unboundLocal 0) => pure ()
  | _ => throw (IO.userError "unbound printer local did not fail explicitly")
  -- Existing input-profile emission remains narrower, with unchanged behavior.
  match Input.emit (← checked (.binary .wordDiv (.var 0) (word 0))) with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "old runtime-input profile unexpectedly changed")

def testSourcePrimitiveEmitter : IO Unit := do
  ordinaryChecks
  boundaryChecks
  byteExponentChecks
  legacyScalarChecks
  formattingChecks
  rejectionChecks

end Tests.SourcePrimitiveEmitter
end
