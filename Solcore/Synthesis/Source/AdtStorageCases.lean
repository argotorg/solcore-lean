import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.AdtStorageEmitter
import Solcore.Synthesis.Stateful.AdtStorageExecution
import Solcore.Synthesis.Stateful.StdCalldata

/-! Enum and struct storage cases retain one original host-aware Core contract,
its type shape, declared methods, key base and step, and an ordered history of
method calls. Each transaction records its method and the arguments it takes.
The observed slots are derived from the shape and the two keys and are part of
the case. Reductions remove transactions, then methods no transaction calls,
then shrink the shape, reduce the step and simplify arguments. Saved outputs
are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.AdtStorage
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload WordType)
open Solcore.Synthesis.Stateful.AdtStorageExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-adt-storage-case.v1"
def planSchema : String := "solcore-lean.adt-storage-plan.v1"
def profileVersion : String := "stateful-adt-storage-v1/adt-storage-sequence-seed-v2"
def templateVersion : String := "std-storage-generic-enum-record-fields-mappings-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-adt-storage-corpus.v1"

/-- Flags and inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- The key bases a generated case draws from; the last wraps to zero. -/
def keyBases : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.ofNatModulo (2 ^ 255), Word.maximum]

/-- Complete contracts may exceed the step budget by the Keccak closure, the
enum closures and the methods. -/
def maxProgramNodes : Nat := 512 + AdtStorage.hashNodes + AdtStorage.maxOutsideNodes

def validTransactions (plan : CheckedPlan) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id && tx.valid plan) = true

instance (plan : CheckedPlan) (transactions : List Transaction) : Decidable (validTransactions plan transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum and struct storage contract exceeds its case limit"
  else throw s!"enum and struct storage scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each calling a declared method with a key of the case, a record field and a variant of the shape where it takes them"

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.AdtStorageExecution.planSlots scenario.plan

def transactionJson (tx : Transaction) : Json := Json.mkObj <|
  [("id", toJson tx.id), ("method", toJson tx.method.name), ("flags", toJson (toString tx.flags.val))] ++
    (if tx.method.keyed then [("key", toJson (toString tx.key.val))] else []) ++
    (if tx.method.updates then [("field", toJson tx.field)] else []) ++
    (if tx.method.takesVariant then [("variant", toJson tx.variant)] else []) ++
    (if tx.method.reads then [] else [("input", toJson (toString tx.input.val))]) ++
    [("calldata", toJson (Solcore.Synthesis.Stateful.AdtStorageExecution.calldata tx)), ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def optionalWord (row : Json) (name : String) : Except String Word :=
  match row.getObjVal? name with
  | .ok value => do word (← value.getStr?)
  | .error _ => pure Word.zero

private def optionalNat (row : Json) (name : String) : Except String Nat :=
  match row.getObjVal? name with
  | .ok value => do
      let number ← value.getNat?
      unless number < 16 do throw "a transaction's field or variant is below sixteen"
      pure number
  | .error _ => pure 0

def decodeTransactions (plan : CheckedPlan) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let name ← row.getObjValAs? String "method"
    let some method := Method.ofName? name | throw "transaction names an unknown method"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", method,
      ← word (← row.getObjValAs? String "flags"), ← optionalWord row "key", ← optionalNat row "field",
      ← optionalNat row "variant", ← optionalWord row "input"⟩
    unless Storage.validId transaction.id && transaction.valid plan do
      throw "invalid transaction ID, undeclared method, or a key, field or variant outside the case"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, method, arguments, calldata or zero-value metadata"
    return transaction
  unless validTransactions plan transactions do
    throw "enum and struct storage scenario requires distinct valid transaction IDs"
  return transactions

def shapeJson (shape : Shape) : Json := Json.mkObj [
  ("variants", toJson (shape.variants.map Payload.name)), ("position", toJson shape.position),
  ("wordType", toJson shape.wordType.name)]

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("shape", shapeJson plan.shape),
  ("methods", toJson (plan.methods.map (·.name))), ("keyBase", toJson (toString plan.keyBase.val)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def decodeShape (json : Json) : Except String Shape := do
  let names ← json.getObjValAs? (List String) "variants"
  unless names.length ≤ AdtStorage.maxVariants do throw "a shape has at most four variants"
  let variants ← names.mapM fun name => match Payload.ofName? name with
    | some payload => pure payload
    | none => throw "unknown variant payload"
  let some wordType := WordType.ofName? (← json.getObjValAs? String "wordType") | throw "unknown Word type"
  let shape : Shape := {variants, position := ← json.getObjValAs? Nat "position", wordType}
  unless shape.valid do
    throw "a shape has two to four variants of zero to three Words or a pair, one payload-free, at most four enum slots and the enum at record position 0, 1 or 2"
  unless json == shapeJson shape do throw "noncanonical shape"
  return shape

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum and struct storage plan schema"
  let shape ← decodeShape (← json.getObjVal? "shape")
  let names ← json.getObjValAs? (List String) "methods"
  unless names.length ≤ Method.all.length do throw "a plan declares at most twelve methods"
  let methods ← names.mapM fun name => match Method.ofName? name with
    | some method => pure method
    | none => throw "plan declares an unknown method"
  let keyBase ← word (← json.getObjValAs? String "keyBase")
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? shape methods keyBase step |
    throw "enum and struct storage plan needs one to twelve distinct methods in declaration order and full host-Core admission"
  unless json == planJson plan do throw "enum and struct storage plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "enum and struct storage contract exceeds its case limit"
  return plan

def emitted (plan : CheckedPlan) : Except String EmittedAdtStorage := (emit plan).mapError reprStr

/-- The layout the Core contract and the observed slots use, recorded for the
adapter to recompute independently. -/
def layoutJson (shape : Shape) : Json := Json.mkObj [
  ("accumulatorSlot", toJson AdtStorage.accumulatorSlot), ("choiceSlot", toJson AdtStorage.choiceSlot),
  ("choiceSlots", toJson shape.choiceSlots), ("recordSlot", toJson shape.recordSlot),
  ("recordSlots", toJson shape.recordSlots),
  ("fieldOffsets", toJson ((List.range AdtStorage.recordFields).map shape.fieldOffset)),
  ("choicesSlot", toJson shape.choiceMapSlot), ("recordsSlot", toJson shape.recordMapSlot),
  ("clearVariant", toJson shape.clearVariant)]

def contractJson (plan : CheckedPlan) (emitted : EmittedAdtStorage) : Json := Json.mkObj [
  ("name", toJson emitted.contractName),
  ("methods", toJson (plan.methods.map fun method => Json.mkObj [
    ("name", toJson method.name), ("signature", toJson method.signature),
    ("selector", toJson (Stateful.StdCalldata.selectorText method.selector)),
    ("parameters", toJson method.parameters)])),
  ("layout", layoutJson plan.shape),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedAdtStorage) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("adtStoragePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson AdtStorage.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let source ← emitted scenario.plan
  return makeCase scenario source origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum and struct storage case schema"
  let plan ← checkedPlan (← json.getObjVal? "adtStoragePlan")
  let transactions ← decodeTransactions plan (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum and struct storage plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") ==
      Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots do
    throw "observed slots must be the accumulator, the enum and record fields and both keys' entry slots"
  return scenario

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.AdtStorageExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Per transaction a method, a variant (taken modulo the variant count), a
record field, a key, a flags bank index and an input bank index, then the
completion pattern. Each choice uses the high half of one draw from a
separate stream. The stream starts at SplitMix64's finalizer of the seed xor its
domain, so that consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := (List.replicate 3 [12, 12, 3, 2, 6, 6]).flatten ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6164747374727371))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 18 0) [false, false, false]

/-- A transaction of the shape and keys from its six choices; arguments the
method does not take are zero. -/
def drawnTransaction (shape : Shape) (keys : List Word) (id : String) (odd : Bool) (choices : List Nat) : Transaction :=
  let method := Method.all.getD (choices.getD 0 0) .getChoice
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  ⟨id, method, parityInput odd (bank 4),
    if method.keyed then keys.getD (choices.getD 3 0) Word.zero else Word.zero,
    if method.updates then choices.getD 2 0 else 0,
    if method.takesVariant then choices.getD 1 0 % shape.count else 0,
    if method.reads then Word.zero else bank 5⟩

def blockTransactions (shape : Shape) (keys : List Word) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    drawnTransaction shape keys ("tx-" ++ toString (first + index)) odd (choices.drop (6 * index))

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (keys : List Word) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape keys) seed count

/-- Separate the shape and key streams from each other and from other uses of
a case seed. -/
private def countDomain : UInt64 := 0x6164747374726301
private def listDomain : UInt64 := 0x6164747374726c01
private def positionDomain : UInt64 := 0x6164747374727001
private def typeDomain : UInt64 := 0x6164747374727401
private def keyDomain : UInt64 := 0x6164747374726b01

private def drawn (seed : Seed) (domain : UInt64) (bound : Nat) : Nat :=
  (GeneratorV2.mix (seed.toUInt64 ^^^ domain)).toNat % bound

/-- SplitMix64 hashes of the seed: the variant count, a list among that
count's valid lists, the enum's position and the Word type, each uniform. -/
def shapeFor (seed : Seed) : Shape :=
  let count := AdtStorage.minVariants + drawn seed countDomain (AdtStorage.maxVariants - AdtStorage.minVariants + 1)
  let lists := AdtStorage.variantLists count
  {variants := lists.getD (drawn seed listDomain lists.length) [], position := drawn seed positionDomain AdtStorage.recordFields,
    wordType := if drawn seed typeDomain 2 == 0 then .word else .uint256}

def keyBaseFor (seed : Seed) : Word := keyBases.getD (drawn seed keyDomain keyBases.length) Word.zero

/-- The methods a sequence calls, in declaration order. -/
def calledMethods (transactions : List Transaction) : List Method :=
  Method.all.filter fun method => transactions.any (·.method == method)

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget; the Keccak closure, the enum closures and
the methods lie outside it. The complete contract is remeasured as the final
budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && AdtStorage.shellNodes < nodes do
    throw "node budget is too small for the enum and struct storage wrapper or exceeds 512"
  let shape := shapeFor seed
  let keyBase := keyBaseFor seed
  let keys := [keyBase, Word.ofNatModulo (keyBase.val + 1)]
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - AdtStorage.shellNodes) revision
  let sequence := generatedTransactions shape keys seed transactions
  let methods := calledMethods sequence
  let some plan := CheckedPlan.ofParts? shape methods keyBase step |
    throw "generated enum and struct storage plan failed full Core admission"
  let scenario ← checkedScenario plan sequence
  unless Wire.programNodes scenario.program ≤
      nodes + AdtStorage.hashNodes + AdtStorage.closureNodes shape + AdtStorage.methodNodes shape methods do
    throw "enum and struct storage contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "adt-storage-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("shape", shapeJson shape), ("keyBase", toJson (toString keyBase.val)), ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum and struct storage history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "enum and struct storage history did not follow its prescribed flags parities"

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
        let source ← emitted scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), source)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "enum and struct storage history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "adt-storage-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, source) =>
          cases := cases.push (makeCase scenario source origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Variants, payload Words, pair payloads and the `uint256` type. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.count + (shape.variants.map Payload.width).sum + (shape.variants.filter (· == .pair)).length +
    (if shape.wordType == .uint256 then 1 else 0)

/-- A transaction's argument values; the key counts as its index among the case's keys. -/
def argumentWeight (plan : CheckedPlan) (tx : Transaction) : Nat :=
  tx.flags.val + tx.input.val + tx.field + tx.variant + (if tx.method.keyed && tx.key != plan.keyBase then 1 else 0)

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + argumentWeight scenario.plan tx) 0

/-- Transaction count, method count, shape weight, complete program
size/literals, then argument values. Every axis is a natural number and the
comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.methods.length < source.plan.methods.length ∨
    (candidate.plan.methods.length = source.plan.methods.length ∧
      (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
      (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
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
  sameKeys : candidate.plan.keyBase = source.plan.keyBase
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

def sealReduction (source : CheckedScenario) (shape : Shape) (methods : List Method) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? shape methods source.plan.keyBase step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if keys : candidate.plan.keyBase = source.plan.keyBase then
        if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
          if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, keys, ids, strict⟩
          else none
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Without variant `removed`, later variants move down by one. -/
private def renumber (removed : Nat) (tx : Transaction) : Transaction :=
  if tx.method.takesVariant && tx.variant > removed then {tx with variant := tx.variant - 1} else tx

/-- The narrower payloads of a variant: a pair as two Words, `k` Words as `k - 1`. -/
private def narrower : Payload → List Payload
  | .pair => [.words 2]
  | .words (count + 1) => [.words count]
  | .words 0 => []

/-- One-transaction removals first, from the last back; then the removal of
each declared method no transaction calls; then shape reductions: removing a
variant no transaction names, narrowing a payload and `uint256` to `word`;
then step reductions; then per transaction the flags' parity bit, smaller bank
inputs, and smaller variant, field and key arguments. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let methods := source.plan.methods
  let step := source.plan.step
  let transactions := source.transactions
  let mut raw : List (Shape × List Method × Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range transactions.length).reverse do
    raw := raw ++ [(shape, methods, step, (transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for method in methods.reverse do
    if transactions.all (·.method != method) then
      raw := raw ++ [(shape, methods.erase method, step, transactions)]
  for index in (List.range shape.count).reverse do
    if transactions.all (fun tx => !tx.method.takesVariant || tx.variant != index) then
      raw := raw ++ [({shape with variants := shape.variants.eraseIdx index}, methods, step, transactions.map (renumber index))]
  for (payload, index) in shape.variants.zipIdx do
    for smaller in narrower payload do
      raw := raw ++ [({shape with variants := shape.variants.set index smaller}, methods, step, transactions)]
  if shape.wordType == .uint256 then
    raw := raw ++ [({shape with wordType := .word}, methods, step, transactions)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(shape, methods, reduced.candidate.function, transactions)]
  for (transaction, index) in transactions.zipIdx do
    raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    for smaller in boundaryInputs do
      if smaller.val < transaction.input.val then
        raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with input := smaller})]
    if transaction.variant > 0 then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with variant := 0})]
    if transaction.field > 0 then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with field := 0})]
    if transaction.method.keyed && transaction.key != source.plan.keyBase then
      raw := raw ++ [(shape, methods, step, replaceAt transactions index fun tx => {tx with key := source.plan.keyBase})]
  let mut seen : List String := []
  let mut result := []
  for (shape, methods, step, transactions) in raw do
    if let some reduced := sealReduction source shape methods step transactions then
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
      ("functionVersion", AdtStorage.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let source ← emitted admitted.plan
  unless (← json.getObjValAs? String "source") = source.source do
    throw "saved source differs from the enum and struct storage emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan source do
    throw "saved contract metadata differs from the enum and struct storage wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do
    throw "saved features differ from the checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "adt-storage-generated" then
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
      throw "saved origin differs from generated enum and struct storage provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.shape admitted.plan.methods admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not keep the step's bindings, the keys and the IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported enum and struct storage case origin"
  return makeCase admitted source origin fuel revision mask

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

end Solcore.Synthesis.Source.AdtStorage
