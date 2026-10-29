import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.ArrayReturnEmitter
import Solcore.Synthesis.Stateful.ArrayReturnExecution

/-! Array-return cases retain one original host-aware Core contract, its array's
shape and an ordered history of `(flags, input, choice, length)` transactions,
every one of which carries the shape's `choice` and `length`. Reductions remove
transactions, drop the last element, change the element type to `uint256`,
shorten inner lengths, reduce the step and simplify flags and inputs; a changed
shape changes every transaction's `choice` and `length` with it. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ArrayReturn
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ArrayReturn (CheckedPlan Element Shape)
open Solcore.Synthesis.Stateful.ArrayReturnExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-array-return-case.v1"
def planSchema : String := "solcore-lean.array-return-plan.v1"
def profileVersion : String := "stateful-array-returns-v1/array-sequence-seed-v1"
def templateVersion : String := "std-array-encode-result-count-last-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-array-return-corpus.v1"

/-- Flags values and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- `bytes` lengths drawn with probability one half: empty, the Word boundaries
and the bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- Complete contracts, shell included, stay within the largest step budget. -/
def maxProgramNodes : Nat := 512

/-- Whether a transaction carries the shape's run-time arguments. -/
def admits (shape : Shape) (transaction : Transaction) : Bool :=
  transaction.length.val == shape.lengthArgument && transaction.choice.val == shape.choiceArgument

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
  s!"array-return scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each with the plan's count as its length and the plan's inner lengths as its choice"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical array-return contract exceeds its case limit"
  else throw transactionRule

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("choice", toJson (toString tx.choice.val)), ("length", toJson (toString tx.length.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.ArrayReturnExecution.calldata tx.flags tx.input tx.choice
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

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("elements", toJson plan.shape.element.name),
  ("count", toJson plan.shape.count), ("lengths", toJson plan.shape.lengths),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported array-return plan schema"
  let some element := Element.ofName? (← json.getObjValAs? String "elements")
    | throw "unsupported array element type"
  let shape : Shape := ⟨element, ← json.getObjValAs? Nat "count", ← json.getObjValAs? (List Nat) "lengths"⟩
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "array-return plan needs at most three elements, one inner length per dynamic element within its bound, and full host-Core admission"
  unless json == planJson plan do throw "array-return plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "array-return contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("arrayReturnPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.ArrayReturnExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ArrayReturn.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic array-return case schema"
  let plan ← checkedPlan (← json.getObjVal? "arrayReturnPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical array-return plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.ArrayReturnExecution.slotsJson do
    throw "observed slots must be zero through two"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.ArrayReturnExecution.observe scenario.plan scenario.transactions bindings fuel

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

/-- The element type, the count, then per element a `bytes` length selector, a
uniform `bytes` length and an inner array's length. -/
def shapeBounds : List Nat := [4, 4, 14, 14, 14, 65, 65, 65, 3, 3, 3]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172722d73686170 shapeBounds

/-- The four element types in the order of the element-type draw. -/
def elementTypes : List Element := [.words, .fourBytes, .bytes, .nested]

/-- An element type and a count, uniformly; a `bytes` length from the bank
when its selector is below seven, else the uniform draw from 0 to 64; an inner
array's length uniformly from 0 to 2. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let element := elementTypes.getD (choices.getD 0 0) .words
  let count := choices.getD 1 0
  let length := fun (index : Nat) => match element with
    | .bytes =>
        let selector := choices.getD (2 + index) 0
        if selector < lengthBank.length then lengthBank.getD selector 0 else choices.getD (5 + index) 0
    | _ => choices.getD (8 + index) 0
  ⟨element, count, if element.dynamic then (List.range count).map length else []⟩

/-- Three flags, three inputs, then the completion pattern. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 4]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172722d73657173 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

/-- A transaction of the shape's run-time arguments. -/
def shaped (shape : Shape) (id : String) (flags input : Word) : Transaction :=
  ⟨id, flags, input, Word.ofNatModulo shape.choiceArgument, Word.ofNatModulo shape.lengthArgument⟩

def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    shaped shape ("tx-" ++ toString (first + index)) (parityInput odd (bank index)) (bank (3 + index))

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
  let shell := Solcore.Synthesis.Core.ArrayReturn.shellNodes shape
  unless nodes ≤ 512 && shell < nodes do
    throw "node budget is too small for the array-return wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - shell) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated array-return plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do
    throw "array-return contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "array-return-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "array-return history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "array-return history did not follow its prescribed flags parities"

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
            error == "array-return history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "array-return-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- `uint256` 0, `bytes4` 1, inner arrays 2 and `bytes` 3. -/
def elementWeight : Element → Nat
  | .words => 0
  | .fourBytes => 1
  | .nested => 2
  | .bytes => 3

def totalLength (shape : Shape) : Nat := shape.lengths.foldl (· + ·) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the element count, the element type's weight, the total
inner length, complete program size/literals, then flags and input values.
Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.shape.count < source.plan.shape.count ∨
    (candidate.plan.shape.count = source.plan.shape.count ∧
      (elementWeight candidate.plan.shape.element < elementWeight source.plan.shape.element ∨
      (elementWeight candidate.plan.shape.element = elementWeight source.plan.shape.element ∧
        (totalLength candidate.plan.shape < totalLength source.plan.shape ∨
        (totalLength candidate.plan.shape = totalLength source.plan.shape ∧
          ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
          (complexity candidate.program.body = complexity source.program.body ∧
            valueWeight candidate < valueWeight source)))))))))

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

/-- The transactions with a new shape's run-time arguments. -/
def reshaped (shape : Shape) (transactions : List Transaction) : List Transaction :=
  transactions.map fun tx => shaped shape tx.id tx.flags tx.input

/-- One-transaction removals, the last element dropped, `uint256` elements,
shorter inner lengths, step reductions, then per transaction the flags' parity
bit and the input's low byte. A changed shape changes every transaction's
arguments with it. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  let mut shapes : List Shape := []
  if shape.count > 0 then
    shapes := shapes ++ [{shape with count := shape.count - 1, lengths := shape.lengths.dropLast}]
  if shape.element != .words then
    shapes := shapes ++ [⟨.words, shape.count, []⟩]
  for (length, index) in shape.lengths.zipIdx do
    let shorter := match shape.element with
      | .bytes => [0, length / 2]
      | _ => [length - 1]
    for value in shorter.eraseDups do
      if value < length then
        shapes := shapes ++ [{shape with lengths := shape.lengths.set index value}]
  for smaller in shapes do
    raw := raw ++ [(source.plan.step, smaller, reshaped smaller source.transactions)]
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
      ("functionVersion", Solcore.Synthesis.Core.ArrayReturn.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from array-return plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from array-return wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "array-return-generated" then
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
      throw "saved origin differs from generated array-return provenance"
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
  else throw "unsupported array-return case origin"
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

end Solcore.Synthesis.Source.ArrayReturn
