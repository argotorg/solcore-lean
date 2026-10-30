import Solcore.Synthesis.Source.EnumArgumentCases
import Solcore.Synthesis.Source.ConstructorArgumentsEmitter
import Solcore.Synthesis.Stateful.ConstructorArgumentsExecution

/-! Constructor-argument cases retain the original host-aware initializer and
runtime contracts, the constructor's parameters, one deployment record with
its malformation, and an ordered history of `(flags, input)` runtime
transactions, none when std rejects the deployment. Each case records std's
prescribed decision on its argument bytes. Reductions remove transactions,
drop or simplify the malformation, shorten a `bytes` length, simplify the
parameters, drop and narrow enum constructors, reduce the step and simplify
the record Words, flags and inputs. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ConstructorArguments
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Stateful.ConstructorArgumentsExecution (Deployment Malformation Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-constructor-argument-case.v1"
def planSchema : String := "solcore-lean.constructor-argument-plan.v1"
def profileVersion : String := "stateful-constructor-arguments-v1/constructor-sequence-seed-v1"
def templateVersion : String := "std-constructor-decode-record-step-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-constructor-argument-corpus.v1"

/-- Flags values, inputs and record Words; the bank of the two-slot storage
profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- `bytes` lengths drawn with probability one half: empty, the Word boundaries
and the bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- The runtime, shell included, stays within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- The initializer lies outside the step budget. -/
def maxInitializerNodes : Nat := 1024

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The record Words a deployment's parameters and choice use: `first` for
`b`, one Word or two, and `second` for two Words or a payload. -/
private def usesFirst (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .words | .bytes => true
  | .enum shape => (Stateful.ConstructorArgumentsExecution.chosen shape deployment).payload != .noWords
  | _ => false

private def usesSecond (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .bytes => true
  | .enum shape => [Payload.twoWords, .pair, .bytes].contains
      (Stateful.ConstructorArgumentsExecution.chosen shape deployment).payload
  | _ => false

/-- A canonical record: a choice below the constructor count, a length of at
most 64 only where a `bytes` value is sent, and zero in every Word the
parameters do not send. -/
def admitsRecord (parameters : Parameters) (deployment : Deployment) : Bool :=
  let choiceOk := match parameters with
    | .enum shape => deployment.choice < shape.constructors.length
    | _ => deployment.choice == 0
  choiceOk && deployment.length ≤ Stateful.ConstructorArgumentsExecution.maxLength &&
    (Stateful.ConstructorArgumentsExecution.carriesBytes parameters deployment || deployment.length == 0) &&
    (parameters != .none || deployment.a == Word.zero) &&
    (usesFirst parameters deployment || deployment.first == Word.zero) &&
    (usesSecond parameters deployment || deployment.second == Word.zero) &&
    deployment.malformation.valid parameters deployment

def rejected (parameters : Parameters) (deployment : Deployment) : Bool :=
  (Stateful.ConstructorArgumentsExecution.stdRejection? parameters deployment).isSome

def validTransactions (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) : Prop :=
  transactions.length ≤ Stateful.Sequence.maxTransactions ∧ (transactions.map (·.id)).Nodup ∧
    transactions.all (fun tx => Storage.validId tx.id) = true ∧ admitsRecord parameters deployment = true ∧
    (rejected parameters deployment = false ∨ transactions = [])

instance (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) :
    Decidable (validTransactions parameters deployment transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  deployment : Deployment
  transactions : List Transaction
  valid : validTransactions plan.parameters deployment transactions
  bounded : Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes
  initializerBounded : Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.runtimeProgram

private def transactionRule : String :=
  s!"constructor-argument scenario requires a canonical deployment record with an applicable malformation, at most {Stateful.Sequence.maxTransactions} runtime transactions with distinct valid IDs, and none after a rejected deployment"

def checkedScenario (plan : CheckedPlan) (deployment : Deployment) (transactions : List Transaction) :
    Except String CheckedScenario := do
  if valid : validTransactions plan.parameters deployment transactions then
    if bounded : Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes then
      if initializerBounded : Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes then
        return ⟨plan, deployment, transactions, valid, bounded, initializerBounded⟩
      else throw "constructor-argument initializer exceeds its case limit"
    else throw "canonical constructor-argument runtime exceeds its case limit"
  else throw transactionRule

def malformationKinds : List String :=
  ["none", "truncate", "trailing", "offset", "length", "tag", "tagCut", "tail", "narrow"]

def kindOf : Malformation → String
  | .none => "none"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .tag _ => "tag"
  | .tagCut _ => "tagCut"
  | .tail _ => "tail"
  | .narrow => "narrow"

abbrev patternNames := Stateful.StdCalldata.patternNames

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .tagCut value => Json.mkObj [("kind", toJson "tagCut"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .narrow => Json.mkObj [("kind", toJson "narrow")]

/-- std's revert data as text: an error selector, `0x` for an unknown tag, or
null when the deployment succeeds. -/
def prescribed (parameters : Parameters) (deployment : Deployment) : Option String :=
  (Stateful.ConstructorArgumentsExecution.stdRejection? parameters deployment).map
    Solcore.ContractRuntime.encodeBytesText

def deploymentJson (parameters : Parameters) (deployment : Deployment) : Json := Json.mkObj [
  ("a", toJson (toString deployment.a.val)), ("choice", toJson deployment.choice),
  ("first", toJson (toString deployment.first.val)), ("second", toJson (toString deployment.second.val)),
  ("length", toJson deployment.length), ("malformation", malformationJson deployment.malformation),
  ("arguments", toJson (Stateful.ConstructorArgumentsExecution.arguments parameters deployment)),
  ("stdRejection", match prescribed parameters deployment with
    | some data => toJson data
    | none => Json.null)]

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Stateful.ConstructorArgumentsExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "deployment or transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value < 2 ^ 32 do throw s!"{key} is out of range"
  return value

private def nameIndex (names : List String) (json : Json) (key : String) : Except String Nat := do
  let name ← json.getObjValAs? String key
  match names.idxOf? name with
  | some index => return index
  | none => throw s!"unknown malformation {key}"

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "none" => return .none
  | "truncate" => return .truncate (← natural json "kept")
  | "trailing" => return .trailing (← natural json "count") (← nameIndex patternNames json "pattern")
  | "offset" => return .offset (← word (← json.getObjValAs? String "value"))
  | "length" => return .length (← word (← json.getObjValAs? String "value"))
  | "tag" => return .tag (← word (← json.getObjValAs? String "value"))
  | "tagCut" => return .tagCut (← word (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← word (← json.getObjValAs? String "value"))
  | "narrow" => return .narrow
  | _ => throw "unknown malformation kind"

def decodeDeployment (parameters : Parameters) (json : Json) : Except String Deployment := do
  let deployment : Deployment := ⟨← word (← json.getObjValAs? String "a"), ← natural json "choice",
    ← word (← json.getObjValAs? String "first"), ← word (← json.getObjValAs? String "second"),
    ← natural json "length", ← decodeMalformation (← json.getObjVal? "malformation")⟩
  unless admitsRecord parameters deployment do throw transactionRule
  unless json == deploymentJson parameters deployment do
    throw "deployment differs from its canonical record, malformation, arguments or std outcome"
  return deployment

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be at most {Stateful.Sequence.maxTransactions}"
  rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, calldata or zero-value metadata"
    return transaction

private def payloadOf? (fields : String) : Option Payload :=
  [Payload.noWords, .oneWord, .twoWords, .pair, .bytes].find? (EnumArgument.fieldsName · == fields)

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("parameters", toJson plan.parameters.name),
  ("constructors", toJson (match plan.parameters with
    | .enum shape => shape.constructors.map EnumArgument.constructorJson
    | _ => [])),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def parametersOf? (name : String) (constructors : List Constructor) : Option Parameters :=
  match name, constructors with
  | "none", [] => some .none
  | "uint256", [] => some .word
  | "uint256,uint256", [] => some .words
  | "uint256,bytes", [] => some .bytes
  | "uint256,enum", list => (EnumArgument.Shape.ofList? list).map Parameters.enum
  | _, _ => none

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported constructor-argument plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  unless rows.size ≤ Solcore.Synthesis.Core.EnumArgument.maxConstructors do
    throw "an enum has at most four constructors"
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some parameters := parametersOf? (← json.getObjValAs? String "parameters") constructors
    | throw "unsupported constructor parameters"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step parameters
    | throw "constructor-argument plan needs valid parameters, an enum of two to four constructors with distinct bank names and at most two with bytes, and full host-Core admission of both contracts"
  unless json == planJson plan do throw "constructor-argument plan differs from its canonical checked representation"
  unless Wire.programNodes plan.runtimeProgram ≤ maxProgramNodes do throw "constructor-argument runtime exceeds its case limit"
  unless Wire.programNodes plan.initializerProgram ≤ maxInitializerNodes do
    throw "constructor-argument initializer exceeds its case limit"
  return plan

def contractJson (parameters : Parameters) (deployment : Deployment) (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson (Stateful.ConstructorArgumentsExecution.arguments parameters deployment))]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("constructorArgumentsPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.plan.runtimeProgram),
    ("initializerProgram", Wire.encodeProgram scenario.plan.initializerProgram),
    ("source", toJson emitted.source),
    ("deployment", deploymentJson scenario.plan.parameters scenario.deployment),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Stateful.ConstructorArgumentsExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
      ("initializerVersion", toJson Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan.parameters scenario.deployment emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

private def decodeProgram (json : Json) (budget : Nat) : Except String Wire.Program :=
  (Wire.decodeProgramWithBudget {maxDepth := 512, maxNodes := budget, maxIntegerBytes := 4096} json).mapError (fun
    | .protocol error => error.toJson.compress
    | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)

/-- Every origin must reconstruct the fixed host contracts, including imports
and reductions. Arbitrary well-typed programs are not admissible
replacements. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic constructor-argument case schema"
  let plan ← checkedPlan (← json.getObjVal? "constructorArgumentsPlan")
  let deployment ← decodeDeployment plan.parameters (← json.getObjVal? "deployment")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let runtime ← decodeProgram (← json.getObjVal? "program") maxProgramNodes
  unless Wire.encodeProgram runtime == Wire.encodeProgram plan.runtimeProgram do
    throw "saved original Core runtime differs from the canonical constructor-argument plan"
  let initializer ← decodeProgram (← json.getObjVal? "initializerProgram") maxInitializerNodes
  unless Wire.encodeProgram initializer == Wire.encodeProgram plan.initializerProgram do
    throw "saved original Core initializer differs from the canonical constructor-argument plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Stateful.ConstructorArgumentsExecution.slotsJson do
    throw "observed slots must be zero through five"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan deployment transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Stateful.ConstructorArgumentsExecution.observe scenario.plan scenario.deployment scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws step by a fixed
residue. -/
private def mixed (value : Nat) : Nat :=
  let z := value % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % 2 ^ 64
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % 2 ^ 64
  z ^^^ (z >>> 31)

/-- High halves of successive draws from the stream that starts at the mixed
`seed` xor `domain`, each below its bound. -/
private def boundedDraws (seed : Seed) (domain : Nat) (bounds : List Nat) : List Nat := Id.run do
  let mut state := Seed.ofNat (mixed (seed.toNat ^^^ domain))
  let mut values : Array Nat := #[]
  for bound in bounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The parameters, `a`, `first` and `second`, the choice, a `bytes` length
selector and uniform length, then the malformation's canonical selector, its
kind and its bank entry. -/
def shapeBounds : List Nat := [8, 6, 6, 6, 12, 14, 65, 3, 12, 16]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6374722d73686170 shapeBounds

/-- `none`, `uint256` and `uint256,uint256` once each of eight, `uint256,bytes`
twice and an enum three times, its shape drawn as for the enum-argument
profile. -/
def generatedParameters (seed : Seed) : Parameters :=
  match (shapeChoices seed).getD 0 0 with
  | 0 => .none
  | 1 => .word
  | 2 => .words
  | 3 | 4 => .bytes
  | _ => .enum (Solcore.Synthesis.Source.EnumArgument.generatedShape seed)

/-- The record with every Word the parameters do not send set to zero, and no
length where no `bytes` value is sent. -/
def canonicalRecord (parameters : Parameters) (deployment : Deployment) : Deployment :=
  let choice := match parameters with
    | .enum shape => deployment.choice % shape.constructors.length
    | _ => 0
  let base := {deployment with choice}
  {base with
    a := if parameters == .none then Word.zero else base.a
    first := if usesFirst parameters base then base.first else Word.zero
    second := if usesSecond parameters base then base.second else Word.zero
    length := if Stateful.ConstructorArgumentsExecution.carriesBytes parameters base then base.length else 0}

private def uniqueNats (values : List Nat) : List Nat := values.eraseDups

/-- The kinds that apply to a record, in catalog order. -/
def malformationBank (parameters : Parameters) (deployment : Deployment) (kind : String) : List Malformation :=
  let n := Stateful.ConstructorArgumentsExecution.canonicalSize parameters deployment
  let valid := fun (malformation : Malformation) => malformation.valid parameters deployment
  let words := fun (values : List Nat) => (uniqueNats values).map w
  (match kind with
    | "truncate" =>
        let boundaries := (List.range ((n + 31) / 32)).filterMap fun index =>
          if 0 < index && 32 * index < n then some index else none
        (uniqueNats (0 :: (boundaries.flatMap fun index => [32 * index - 1, 32 * index]) ++ [n - 1])).map Malformation.truncate
    | "trailing" => [1, 31, 32, 33].flatMap fun count => [0, 1, 2].map (Malformation.trailing count)
    | "offset" => (words [0, 32, n - 31, n, 2 ^ 255, 2 ^ 256 - 32]).map Malformation.offset
    | "length" =>
        let length := deployment.length
        let fits := n - (Stateful.ConstructorArgumentsExecution.lengthPosition parameters + 32)
        (words ([0] ++ (if length > 0 then [length - 1] else []) ++ [length + 1, fits, fits + 1, 2 ^ 256 - 1])).map Malformation.length
    | "tag" | "tagCut" =>
        let tag := match parameters with
          | .enum shape => (EnumArgument.tag (Stateful.ConstructorArgumentsExecution.chosen shape deployment)).val
          | _ => 0
        let values := words [0, tag + 1, tag ^^^ 2 ^ 255, 2 ^ 256 - 1]
        if kind == "tag" then values.map Malformation.tag else values.map Malformation.tagCut
    | "tail" =>
        let body := match parameters with
          | .enum shape => Stateful.ConstructorArgumentsExecution.bodyStart shape
          | _ => 0
        (words [0, 32, n - body + 1, 2 ^ 256 - 1]).map Malformation.tail
    | "narrow" => [.narrow]
    | _ => []).filter valid

def applicableKinds (parameters : Parameters) (deployment : Deployment) : List String :=
  (malformationKinds.drop 1).filter fun kind => !(malformationBank parameters deployment kind).isEmpty

/-- Canonical when the selector draw is 0, otherwise a kind uniformly among
those that apply, then an entry of its bank uniformly. -/
def generatedDeployment (seed : Seed) (parameters : Parameters) : Deployment :=
  let choices := shapeChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  let selector := choices.getD 5 0
  let length := if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD 6 0
  let record := canonicalRecord parameters ⟨bank 1, choices.getD 4 0, bank 2, bank 3, length, .none⟩
  if choices.getD 7 0 == 0 then record
  else
    let kinds := applicableKinds parameters record
    match kinds with
    | [] => record
    | _ =>
        let kind := kinds.getD (choices.getD 8 0 % kinds.length) "none"
        let entries := malformationBank parameters record kind
        {record with malformation := entries.getD (choices.getD 9 0 % entries.length) .none}

/-- Three flags, three inputs, then the completion pattern. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6374722d73657173 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index), bank (3 + index)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete runtime is remeasured
as the final budget authority. A rejected deployment ends the scenario, so it
keeps no transactions. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.ConstructorArguments.shellNodes < nodes do
    throw "node budget is too small for the constructor-argument runtime or exceeds 512"
  let parameters := generatedParameters seed
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - Solcore.Synthesis.Core.ConstructorArguments.shellNodes) revision
  let some plan := CheckedPlan.ofParts? step parameters | throw "generated constructor-argument plan failed full Core admission"
  let deployment := generatedDeployment seed parameters
  let sequence := if rejected parameters deployment then [] else generatedTransactions seed transactions
  let scenario ← checkedScenario plan deployment sequence
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "constructor-argument runtime exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "constructor-argument-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "constructor-argument history exhausted Core fuel"
  let deployment ← observed.getObjVal? "deployment"
  let expected := if rejected scenario.plan.parameters scenario.deployment then "reverted" else "returned"
  unless rowStatus deployment == some expected do
    throw "constructor-argument deployment did not follow its prescribed std outcome"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map rowStatus == scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "constructor-argument history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "constructor-argument history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "constructor-argument-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- `none` 0, `uint256` 1, `uint256,uint256` 2, `uint256,bytes` 3 and an enum
4. -/
def parametersWeight : Parameters → Nat
  | .none => 0
  | .word => 1
  | .words => 2
  | .bytes => 3
  | .enum _ => 4

def shapeWeight : Parameters → Nat
  | .enum shape => Solcore.Synthesis.Source.EnumArgument.shapeWeight shape
  | _ => 0

/-- Nothing for no malformation, otherwise one plus its position in its kind's
bank, or one plus the bank's size outside it. -/
def malformationWeight (parameters : Parameters) (deployment : Deployment) : Nat :=
  match deployment.malformation with
  | .none => 0
  | malformation =>
      let bank := malformationBank parameters deployment (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.deployment.a.val + scenario.deployment.first.val + scenario.deployment.second.val +
    scenario.transactions.foldl (fun total tx => total + tx.flags.val + tx.input.val) 0

/-- Transaction count, the parameters, the enum's shape, the malformation's
weight, the `bytes` length, complete program size/literals, then the record
Words, flags and inputs. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (parametersWeight candidate.plan.parameters < parametersWeight source.plan.parameters ∨
    (parametersWeight candidate.plan.parameters = parametersWeight source.plan.parameters ∧
      (shapeWeight candidate.plan.parameters < shapeWeight source.plan.parameters ∨
      (shapeWeight candidate.plan.parameters = shapeWeight source.plan.parameters ∧
        (malformationWeight candidate.plan.parameters candidate.deployment <
            malformationWeight source.plan.parameters source.deployment ∨
        (malformationWeight candidate.plan.parameters candidate.deployment =
            malformationWeight source.plan.parameters source.deployment ∧
          (candidate.deployment.length < source.deployment.length ∨
          (candidate.deployment.length = source.deployment.length ∧
            ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
            (complexity candidate.program.body = complexity source.program.body ∧
              valueWeight candidate < valueWeight source)))))))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (parameters : Parameters)
    (deployment : Deployment) (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step parameters
  let candidate ← (checkedScenario plan deployment transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- New parameters' record and transactions: the record made canonical, a
malformation that no longer applies dropped, and no transactions after a
rejected deployment. -/
def reanchor (parameters : Parameters) (deployment : Deployment) (transactions : List Transaction) :
    Deployment × List Transaction :=
  let record := canonicalRecord parameters {deployment with malformation := .none}
  let kept := if deployment.malformation.valid parameters record then {record with malformation := deployment.malformation}
    else record
  (kept, if rejected parameters kept then [] else transactions)

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The next narrower fields: the struct to two Words, two Words to one, one
Word to none and `bytes` to none. -/
private def narrower : Payload → Option Payload
  | .pair => some .twoWords
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .bytes => some .noWords
  | .noWords => none

/-- Simpler parameters: a static enum, `uint256,bytes` and `uint256,uint256`
become `uint256`, which becomes `none`. -/
private def simpler : Parameters → Option Parameters
  | .enum shape => if shape.dynamic then none else some .word
  | .bytes | .words => some .word
  | .word => some .none
  | .none => none

/-- One-transaction removals, a dropped or earlier malformation, a shorter
length, simpler parameters, dropped and narrowed enum constructors, step
reductions, zero record Words, then the flags' parity bit and the input's low
byte. Candidates still need execution to establish that they preserve a
finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let parameters := source.plan.parameters
  let deployment := source.deployment
  let mut raw : List (Aggregates.CheckedDAG × Parameters × Deployment × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, parameters, deployment,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  let bank := malformationBank parameters deployment (kindOf deployment.malformation)
  let earlier := match bank.idxOf? deployment.malformation with
    | some position => bank.take position
    | none => bank
  for malformation in Malformation.none :: earlier do
    if malformation != deployment.malformation then
      let (kept, transactions) := reanchor parameters {deployment with malformation} source.transactions
      raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  -- A shorter length, empty or halved.
  for shorter in [0, deployment.length / 2] do
    if shorter < deployment.length then
      let (kept, transactions) := reanchor parameters {deployment with length := shorter} source.transactions
      raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  if let some smaller := simpler parameters then
    let (kept, transactions) := reanchor smaller deployment source.transactions
    raw := raw ++ [(source.plan.step, smaller, kept, transactions)]
  if let .enum shape := parameters then
    for index in List.range shape.constructors.length do
      if index != deployment.choice then
        if let some smaller := EnumArgument.Shape.ofList? (shape.constructors.eraseIdx index) then
          let (kept, transactions) := reanchor (.enum smaller)
            {deployment with choice := moveDown index deployment.choice} source.transactions
          raw := raw ++ [(source.plan.step, .enum smaller, kept, transactions)]
    for index in List.range shape.constructors.length do
      if let some constructor := shape.constructors[index]? then
        if let some payload := narrower constructor.payload then
          if let some smaller := EnumArgument.Shape.ofList? (shape.constructors.set index {constructor with payload}) then
            let (kept, transactions) := reanchor (.enum smaller) deployment source.transactions
            raw := raw ++ [(source.plan.step, .enum smaller, kept, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, parameters, deployment, source.transactions)]
  for change in [fun (record : Deployment) => {record with a := Word.zero},
      fun (record : Deployment) => {record with first := Word.zero},
      fun (record : Deployment) => {record with second := Word.zero}] do
    let (kept, transactions) := reanchor parameters (change deployment) source.transactions
    raw := raw ++ [(source.plan.step, parameters, kept, transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, parameters, deployment, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, parameters, deployment, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, parameters, deployment, transactions) in raw do
    if let some reduced := sealReduction source step parameters deployment transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("deployment", deploymentJson reduced.candidate.plan.parameters reduced.candidate.deployment),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentDeployment", deploymentJson parent.plan.parameters parent.deployment),
  ("parentTransactions", transactionsJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.ConstructorArguments.runtimeVersion),
      ("initializerVersion", Solcore.Synthesis.Core.ConstructorArguments.initializerVersion),
      ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from constructor-argument plan emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.parameters admitted.deployment emitted do
    throw "saved contract metadata differs from constructor-argument wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "constructor-argument-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated constructor-argument provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        deploymentJson expected.plan.parameters expected.deployment ==
          deploymentJson admitted.plan.parameters admitted.deployment &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan, deployment or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentDeployment ← decodeDeployment parentPlan.parameters (← origin.getObjVal? "parentDeployment")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentDeployment parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.parameters admitted.deployment
        admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported constructor-argument case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.ConstructorArguments
