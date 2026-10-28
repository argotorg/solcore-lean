import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.EnumReturnEmitter
import Solcore.Synthesis.Stateful.EnumReturnExecution

/-! Enum-return cases retain one original host-aware Core contract, its enum's
constructors, and an ordered history of `(flags, input, choice, length)`
transactions. Reductions remove transactions, shorten lengths, drop unchosen
constructors, narrow fields, reduce the step and simplify flags and inputs.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (EnumPayload)
open Solcore.Synthesis.Core.EnumReturn (CheckedPlan Constructor Shape)
open Solcore.Synthesis.Stateful.EnumReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-enum-return-case.v1"
def planSchema : String := "solcore-lean.enum-return-plan.v1"
def profileVersion : String := "stateful-enum-returns-v1/enum-sequence-seed-v1"
def templateVersion : String := "enum-result-count-last-choice-length-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-enum-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Lengths drawn with probability one half: empty, the Word boundaries and the
bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- Whether constructor `choice` of the shape exists and a nonzero length names
its `bytes` field. -/
def admits (shape : Shape) (transaction : Transaction) : Bool :=
  match shape.constructors[transaction.choice.val]? with
  | some constructor =>
      transaction.length.val ≤ Solcore.Synthesis.Core.EnumReturn.maxLength &&
        (constructor.payload == .boundedBytes || transaction.length.val == 0)
  | none => false

def validTransactions (shape : Shape) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (admits shape) = true

instance (shape : Shape) (transactions : List Transaction) : Decidable (validTransactions shape transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.shape transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

private def transactionRule : String :=
  s!"enum-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, a choice below the constructor count, and a length of at most {Solcore.Synthesis.Core.EnumReturn.maxLength} that only a bytes constructor's transaction may set"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum-return contract exceeds its case limit"
  else throw transactionRule

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("choice", toJson (toString tx.choice.val)), ("length", toJson (toString tx.length.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.EnumReturnExecution.calldata tx.flags tx.input tx.choice
    tx.length)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json :=
  toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (shape : Shape) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input"),
      ← word (← row.getObjValAs? String "choice"), ← word (← row.getObjValAs? String "length")⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, input, choice, length, calldata or zero-value metadata"
    return transaction
  unless validTransactions shape transactions do throw transactionRule
  return transactions

def constructorJson (constructor : Constructor) : Json := Json.mkObj [
  ("name", toJson constructor.name),
  ("fields", toJson (Solcore.Synthesis.Core.EnumReturn.fieldSignature constructor.payload))]

private def payloadOf? (fields : String) : Option EnumPayload :=
  [EnumPayload.noWords, .oneWord, .twoWords, .boundedBytes].find?
    (Solcore.Synthesis.Core.EnumReturn.fieldSignature · == fields)

/-- The constructors of a list of two or more, in order. -/
def Shape.ofList? : List Constructor → Option Shape
  | first :: second :: rest => some ⟨first, second, rest⟩
  | _ => none

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constructors", toJson (plan.shape.constructors.map constructorJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum-return plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some shape := Shape.ofList? constructors | throw "an enum needs at least two constructors"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "enum-return plan needs two to four constructors with distinct bank names, at most two with bytes, and full host-Core admission"
  unless json == planJson plan do throw "enum-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "enum-return contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.EnumReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.EnumReturn.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumReturnPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.EnumReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EnumReturnExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer. The generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose low draw bits follow each
other: a raw shape stream alternates between two `bytes` counts. -/
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

/-- The constructor count, the `bytes` count, four Word fields, two `bytes`
positions and four name indices into the shrinking bank. -/
def shapeBounds : List Nat := [3, 4, 3, 3, 3, 3, 4, 4, 8, 7, 6, 5]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x656e756d2d736870 shapeBounds

/-- Names drawn from the bank without repetition: each index picks among the
names still left. -/
private def drawNames (indices : List Nat) : List String := Id.run do
  let mut left := Solcore.Synthesis.Core.EnumReturn.nameBank
  let mut names : Array String := #[]
  for index in indices do
    names := names.push (left.getD index "")
    left := left.eraseIdx index
  return names.toList

/-- Two to four constructors; none carries `bytes` for a `bytes` draw below 2,
otherwise one or two do, at distinct positions. The other fields are none, one
or two Words. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let count := 2 + choices.getD 0 0
  let bytesCount := choices.getD 1 0 - 1
  let firstBytes := choices.getD 6 0 % count
  let secondBytes := (firstBytes + 1 + choices.getD 7 0 % (count - 1)) % count
  let payloads := (List.range count).map fun index =>
    if (bytesCount ≥ 1 && index == firstBytes) || (bytesCount ≥ 2 && index == secondBytes) then
      EnumPayload.boundedBytes
    else [EnumPayload.noWords, .oneWord, .twoWords].getD (choices.getD (2 + index) 0) .noWords
  let names := drawNames ((choices.drop 8).take count)
  let constructors := (names.zip payloads).map fun (name, payload) => ({name, payload} : Constructor)
  (Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

/-- Three flags, three inputs, the completion pattern, three choices, then per
transaction a length selector and a uniform length. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4, 12, 12, 12, 14, 14, 14, 65, 65, 65]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x656e756d732d7371 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

/-- A selector below seven picks that entry of the length bank; otherwise the
uniform draw from 0 to 64 is the length. -/
def generatedLength (choices : List Nat) (index : Nat) : Nat :=
  let selector := choices.getD (10 + index) 0
  if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD (13 + index) 0

/-- A choice draw below 12 is uniform below any count from 2 to 4; only a
`bytes` constructor's transaction keeps its length. -/
def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let choice := choices.getD (7 + index) 0 % shape.constructors.length
    let carries := shape.constructors[choice]?.any (·.payload == .boundedBytes)
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index), bank (3 + index),
      Word.ofNatModulo choice, Word.ofNatModulo (if carries then generatedLength choices index else 0)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget, and the complete contract is remeasured as
the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let shape := generatedShape seed
  let shell := Solcore.Synthesis.Core.EnumReturn.shellNodes shape
  unless nodes ≤ 512 && shell < nodes do
    throw "node budget is too small for the enum-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated enum-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "enum-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "enum-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "enum-return history did not follow its prescribed flags parities"

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
            error == "enum-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- One per constructor and its fields' weight: none 0, one Word 1, two Words 2
and `bytes` 3. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.constructors.foldl (fun total constructor => total + 1 + match constructor.payload with
    | .noWords => 0
    | .oneWord => 1
    | .twoWords => 2
    | .boundedBytes => 3) 0

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.length.val) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the shape's weight, the total length, complete program
size/literals, then flags and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
    (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
      (totalLength candidate < totalLength source ∨
      (totalLength candidate = totalLength source ∧
        ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
        (complexity candidate.program.body = complexity source.program.body ∧
          valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (shape : Shape)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step shape
  let candidate ← (checkedScenario plan transactions).toOption
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

/-- The shape without constructor `index`, and the transactions' choices above
it moved down. -/
private def dropConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let shape ← Shape.ofList? (shape.constructors.eraseIdx index)
  return (shape, transactions.map fun tx =>
    if tx.choice.val > index then {tx with choice := Word.ofNatModulo (tx.choice.val - 1)} else tx)

/-- The next narrower fields: two Words to one, one Word to none and `bytes`
to none. -/
private def narrower : EnumPayload → Option EnumPayload
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .boundedBytes => some .noWords
  | .noWords => none

/-- Constructor `index` with narrower fields; a `bytes` constructor's
transactions lose their lengths. -/
private def narrowConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let constructor ← shape.constructors[index]?
  let payload ← narrower constructor.payload
  let shape ← Shape.ofList? (shape.constructors.set index {constructor with payload})
  return (shape, transactions.map fun tx =>
    if tx.choice.val == index then {tx with length := Word.zero} else tx)

/-- One-transaction removals, shorter lengths, dropped and narrowed
constructors, step reductions, then per transaction the flags' parity bit and
the input's low byte. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  -- A shorter length, empty or halved, keeps every effect of its transaction.
  for (transaction, index) in source.transactions.zipIdx do
    for shorter in [0, transaction.length.val / 2] do
      if shorter < transaction.length.val then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with length := Word.ofNatModulo shorter})]
  -- A constructor no transaction chooses can go while two others remain.
  for index in List.range shape.constructors.length do
    unless source.transactions.any (·.choice.val == index) do
      if let some (smaller, transactions) := dropConstructor shape source.transactions index then
        raw := raw ++ [(source.plan.step, smaller, transactions)]
  for index in List.range shape.constructors.length do
    if let some (smaller, transactions) := narrowConstructor shape source.transactions index then
      raw := raw ++ [(source.plan.step, smaller, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, shape, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo 255)})]
  let mut seen : List String := []
  let mut result := []
  for (step, shape, transactions) in raw do
    if let some reduced := sealReduction source step shape transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.EnumReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from enum-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from enum-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "enum-return-generated" then
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
      throw "saved origin differs from generated enum-return provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.shape (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.shape admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum-return case origin"
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

end Solcore.Synthesis.Source.EnumReturn
