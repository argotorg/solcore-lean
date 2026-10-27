import Lean.Data.Json
import Solcore.Core.Machine
import Solcore.Synthesis.Core.Generator
import Solcore.Synthesis.Core.Shrink
import Solcore.Synthesis.Source.Emitter

/-! Replayable source cases retain the original checked Core computation.
Observations use the existing Core machine. Source emission is independently
checked by the Rust compiler in the external comparison runner. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source
open Lean
open Solcore.Synthesis.Core

def caseSchema : String := "solcore-lean.semantic-case.v1"
def corpusSchema : String := "solcore-lean.semantic-corpus.v1"

def featureName : Feature → String
  | .wordLiteral => "wordLiteral"
  | .boolLiteral => "boolLiteral"
  | .local => "local"
  | .letE => "let"
  | .ifE => "if"
  | .unary op => "unary:" ++ reprStr op
  | .binary op => "binary:" ++ reprStr op
  | .ternary op => "ternary:" ++ reprStr op

/-- Evaluate the original closed G0 expression, without Rust lowering. -/
def observe (checked : CheckedWordProgram) (fuel : Nat) : Json :=
  let fields := match checked.program.toCore.runStateful fuel with
    | .done (.word word) _ =>
        [("status", toJson "returned"), ("word", toJson (toString word.val))]
    | .done value _ =>
        [("status", toJson "invalid-result"), ("detail", toJson (reprStr value))]
    | .outOfFuel _ => [("status", toJson "out-of-fuel")]
    | .fault reason _ =>
        [("status", toJson "core-fault"), ("detail", toJson (reprStr reason))]
  Json.mkObj (("stage", toJson "execution") :: fields)

def maskJson (mask : FeatureMask) : Json := toJson (mask.enabled.map featureName)

/-- Revision three records its swarm mask in the provenance; the others record none. -/
def swarmField (revision : GeneratorRevision) (mask : FeatureMask) : List (String × Json) :=
  if revision = .v3 then [("swarmMask", maskJson mask)] else []

/-- The mask a saved provenance records: required for revision three, absent otherwise. -/
def savedMask (provenance : Json) (revision : GeneratorRevision) : Except String FeatureMask :=
  match provenance.getObjVal? "swarmMask", revision with
  | .error _, .v3 => throw "revision three requires a swarm mask"
  | .error _, _ => pure FeatureMask.all
  | .ok value, .v3 => do
      let names ← value.getArr?
      let features ← names.toList.mapM fun name => do
        let name ← name.getStr?
        let some feature := FeatureMask.catalog.find? (featureName · = name) |
          throw "unknown swarm mask feature"
        pure feature
      let some mask := FeatureMask.ofFeatures? features | throw "noncanonical swarm mask"
      pure mask
  | .ok _, _ => throw "a swarm mask requires revision three"

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName),
  ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature),
  ("deployPath", toJson emitted.deployPath),
  ("runtimePath", toJson emitted.runtimePath),
  ("calldata", toJson "0xc0406226"),
  ("constructorCalldata", toJson "0x")]

def makeCase (checked : CheckedWordProgram) (emitted : EmittedProgram)
    (origin : Json) (fuel : Nat) (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Json := Json.mkObj [
  ("schema", toJson caseSchema),
  ("program", Solcore.Core.Wire.encodeProgram checked.program),
  ("source", toJson emitted.source),
  ("provenance", Json.mkObj <| swarmField revision mask ++ [
    ("origin", origin),
    ("generatorVersion", toJson revision.version),
    ("emitterVersion", toJson emitterVersion),
    ("wrapperVersion", toJson wrapperVersion),
    ("features", toJson ((features checked.program.body).map featureName))]),
  ("contract", contractJson emitted),
  ("executionFuel", toJson fuel),
  ("directCore", observe checked fuel)]

def emitCase (checked : CheckedWordProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1)
    (mask : FeatureMask := FeatureMask.all) : Except EmitError Json := do
  let emitted ← emit checked
  return makeCase checked emitted origin fuel revision mask

/--
The G0 revision named by saved provenance. An unknown version yields `v1`,
whose exact version check then rejects the case as before.
-/
def savedRevision (provenance : Json) (field : String := "generatorVersion") : GeneratorRevision :=
  match provenance.getObjValAs? String field with
  | .ok version => (GeneratorRevision.ofVersion? version).getD .v1
  | .error _ => .v1

/-- Bounded seed search with one G0 revision; `v1` stays the default. -/
def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let mask := revision.caseMask seed
      match generate {seed, maxProgramNodes := nodes, revision, mask} with
      | .error error =>
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)),
            ("stage", toJson "generation"), ("reason", toJson (reprStr error))])
      | .ok generated =>
          let origin := Json.mkObj [
            ("kind", toJson "generated"),
            ("seed", toJson (toString generated.initialSeed.toNat)),
            ("finalSeed", toJson (toString generated.finalSeed.toNat)),
            ("maxProgramNodes", toJson generated.maxProgramNodes)]
          match emitCase generated.checkedProgram origin fuel revision mask with
          | .error error =>
              excluded := excluded.push (Json.mkObj [
                ("seed", toJson (toString seed.toNat)),
                ("stage", toJson "emission"), ("reason", toJson (reprStr error))])
          | .ok value => cases := cases.push value
  return Json.mkObj [
    ("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def checkedProgram (json : Json) : Except String CheckedWordProgram := do
  let program ← (Solcore.Core.Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096} json).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Solcore.Core.Wire.programNodes program ≤ 512 do
    throw "Core program exceeds the 512-node case limit"
  let some checked := CheckedWordProgram.ofProgram? program |
    throw "program is not a checked closed G0 Word program"
  return checked

def caseProgram (json : Json) : Except String CheckedWordProgram := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic case schema"
  checkedProgram (← json.getObjVal? "program")

/-- Recheck and re-emit saved cases; the saved expected result is never trusted. -/
def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  let checked ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  unless (← provenance.getObjValAs? String "generatorVersion") = revision.version do
    throw "generator version changed"
  unless (← provenance.getObjValAs? String "emitterVersion") = emitterVersion do
    throw "emitter version changed"
  unless (← provenance.getObjValAs? String "wrapperVersion") = wrapperVersion do
    throw "wrapper version changed"
  let origin ← provenance.getObjVal? "origin"
  let mask ← savedMask provenance revision
  let emitted ← (emit checked).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from emission of the original Core program"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the fixed wrapper"
  unless (← provenance.getObjVal? "features") ==
      toJson ((features checked.program.body).map featureName) do
    throw "saved features differ from the original Core program"
  let kind ← origin.getObjValAs? String "kind"
  unless kind = "generated" || kind = "imported" || kind = "reduced" do
    throw "unsupported case origin"
  if kind = "generated" then
    let seedText ← origin.getObjValAs? String "seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do
      throw "saved swarm mask differs from its generation seed"
    let nodes ← origin.getObjValAs? Nat "maxProgramNodes"
    unless nodes ≤ 512 do throw "saved generation budget exceeds limit"
    let generated ←
      (generate {seed := Seed.ofNat seed, maxProgramNodes := nodes, revision, mask}).mapError reprStr
    unless Solcore.Core.Wire.encodeProgram generated.program ==
        Solcore.Core.Wire.encodeProgram checked.program do
      throw "saved program differs from its generation seed"
    unless (← origin.getObjValAs? String "finalSeed") = toString generated.finalSeed.toNat do
      throw "saved final seed differs from generation"
  return makeCase checked emitted origin fuel revision mask

/-- Reduced candidates keep the parent's G0 revision. -/
def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let checked ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let mut results : Array Json := #[]
  for candidate in (shrink checked).take limit do
    let origin := Json.mkObj [
      ("kind", toJson "reduced"),
      ("parentProgram", Solcore.Core.Wire.encodeProgram checked.program)]
    let result ← (emitCase candidate.checkedProgram origin fuel revision mask).mapError reprStr
    results := results.push result
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", .arr results)]

end Solcore.Synthesis.Source
