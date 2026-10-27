import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.NestedArrayCases
import Solcore.Synthesis.Stateful.MalformedNestedArrayExecution

/-! Malformed-nested-array cases retain the std-modeling original Core contract
around a checked aggregate step and an ordered history of nested-array calls,
each with one malformation of its calldata. Canonical values have at most four
rows of at most three elements. The compiled contract is the nested-array one,
emitted from the same step. Every transaction records its malformation, the
calldata it sends and the outcome std prescribes for those bytes. Reductions
remove transactions, simplify the step, drop or simplify a malformation, and
then reduce rows, elements and flags. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MalformedNestedArray
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.MalformedNestedArray (CheckedPlan guardNodes)
open Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
  (Malformation Transaction Bindings stdRejection? maxRows maxColumns tableStart rowStart)

def caseSchema : String := "solcore-lean.semantic-malformed-nested-array-case.v1"
def planSchema : String := "solcore-lean.malformed-nested-array-plan.v1"
def profileVersion : String := "stateful-malformed-nested-array-v1/malformation-sequence-seed-v1"
def templateVersion : String := "std-dispatch-lazy-nested-fold-slots-counts-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-malformed-nested-array-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs
abbrev emitterVersion := NestedArray.emitterVersion
abbrev wrapperVersion := NestedArray.wrapperVersion

/-- Complete contracts may exceed the step budget by the fixed row checks and guards. -/
def maxProgramNodes : Nat := 512 + guardNodes

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "offset", "length", "row-offset", "row-length"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .rowOffset _ _ => "row-offset"
  | .rowLength _ _ => "row-length"

/-- The row a row malformation replaces a Word of. -/
def rowOf : Malformation → Option Nat
  | .rowOffset row _ | .rowLength row _ => some row
  | _ => none

abbrev patternNames := Stateful.StdCalldata.patternNames

def canonicalSize (tx : Transaction) : Nat :=
  (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.canonicalBytes tx).size

def validValue (values : List (List Word)) : Bool :=
  values.length ≤ maxRows && values.all (·.length ≤ maxColumns)

def validTransaction (tx : Transaction) : Bool :=
  Storage.validId tx.id && validValue tx.values &&
    tx.malformation.valid tx.values (canonicalSize tx) &&
    (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.inputBytes tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all validTransaction = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical malformed-nested-array contract exceeds its case limit"
  else throw s!"malformed-nested-array scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, at most four rows of three elements and a valid malformation of at most 1 KiB each"

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .rowOffset row value => Json.mkObj [("kind", toJson "row-offset"), ("row", toJson row),
      ("value", toJson (toString value.val))]
  | .rowLength row value => Json.mkObj [("kind", toJson "row-length"), ("row", toJson row),
      ("value", toJson (toString value.val))]

abbrev selectorText := Stateful.StdCalldata.selectorText

def prescribed (tx : Transaction) : Option Nat :=
  stdRejection? (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.inputBytes tx)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun row => row.map fun value => toString value.val)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.calldata tx)),
  ("stdRejection", match prescribed tx with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value ≤ 2 ^ 32 do throw ("malformation " ++ key ++ " is out of range")
  return value

def decodeMalformation (json : Json) : Except String Malformation := do
  let kind ← json.getObjValAs? String "kind"
  if kind = "none" then return .none
  else if kind = "short" then return .short (← natural json "bytes")
  else if kind = "selector" then
    let text ← json.getObjValAs? String "mask"
    unless text.length ≤ 10 do throw "selector mask exceeds 32 bits"
    let some mask := text.toNat? | throw "invalid selector mask"
    return .selector mask
  else if kind = "truncate" then return .truncate (← natural json "kept")
  else if kind = "trailing" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := patternNames.idxOf? name | throw "unknown trailing pattern"
    return .trailing (← natural json "count") pattern
  else if kind = "offset" then return .offset (← word (← json.getObjValAs? String "value"))
  else if kind = "length" then return .length (← word (← json.getObjValAs? String "value"))
  else if kind = "row-offset" then
    return .rowOffset (← natural json "row") (← word (← json.getObjValAs? String "value"))
  else if kind = "row-length" then
    return .rowLength (← natural json "row") (← word (← json.getObjValAs? String "value"))
  else throw "unknown malformation kind"

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List (List String)) "values"
    unless texts.length ≤ maxRows && texts.all (·.length ≤ maxColumns) do
      throw "value exceeds four rows of three elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM (·.mapM word),
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransaction transaction do throw "invalid transaction ID, values or malformation"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "malformed-nested-array scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

/-- The nested-array plan of the same step, whose source is the compiled contract. -/
def nestedPlan (plan : CheckedPlan) : Except String Solcore.Synthesis.Core.NestedArray.CheckedPlan := do
  let some nestedPlan := Solcore.Synthesis.Core.NestedArray.CheckedPlan.ofStep? plan.step |
    throw "the step fails the nested-array contract's admission"
  return nestedPlan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported malformed-nested-array plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "malformed-nested-array contract failed full host-Core admission"
  unless json == planJson plan do throw "malformed-nested-array plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "malformed-nested-array contract exceeds its case limit"
  let _ ← nestedPlan plan
  return plan

def emit (plan : CheckedPlan) : Except String EmittedProgram := do
  (NestedArray.emit (← nestedPlan plan)).mapError reprStr

abbrev contractJson := NestedArray.contractJson
abbrev initialStateJson := NestedArray.initialStateJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("malformedNestedArrayPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.MalformedNestedArray.version),
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
  let emitted ← emit scenario.plan
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic malformed-nested-array case schema"
  let plan ← checkedPlan (← json.getObjVal? "malformedNestedArrayPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical malformed-nested-array plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.slotsJson do
    throw "observed slots must be zero through eight"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.observe scenario.plan scenario.transactions bindings fuel

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The malformations a transaction draws from, by kind, for row `row` of its
canonical values: none; short calldata; wrong selectors; cuts in the head,
the outer length, the offset table, the last row and the last Word; trailing
bytes; out-of-range, wrapping and overlapping head offsets; too long,
wrapping, maximal, shorter and zero outer lengths; out-of-range, wrapping and
overlapping table Words of the row; and too long, wrapping, shorter and zero
lengths of the row. Changes that leave the canonical calldata as it is and cuts
outside it are left out. -/
def malformationBank (values : List (List Word)) (size row : Nat) : List (List Malformation) :=
  let rows := values.length
  let offsets := Solcore.Synthesis.Stateful.NestedArrayExecution.rowOffsets values
  let entry := offsets.getD row 0
  let other := offsets.getD ((row + 1) % max rows 1) 0
  let width := (values.getD row []).length
  let start := rowStart values row
  let fits := (size - (start + 32)) / 32
  let cuts := ([4, 36, 67, 99, tableStart + 16] ++
      (if rows = 0 then [] else [rowStart values (rows - 1) + 16]) ++ [size - 32, size - 1]).eraseDups.filter
    fun kept => 4 ≤ kept && kept < size
  let rowKinds : List (List Malformation) := if row < rows then [
      ([size - tableStart - 31, size - tableStart, size - tableStart + 1, 2 ^ 255, 2 ^ 256 - 32, 2 ^ 256 - 1, 0,
        other, other + 32].eraseDups.filter (· != entry)).map (.rowOffset row ∘ w),
      ([width + 1, fits, fits + 1, 2 ^ 251, 2 ^ 251 + 1, 2 ^ 256 - 1, width - 1, 0].eraseDups.filter
        (· != width)).map (.rowLength row ∘ w)]
    else [[], []]
  [[.none],
    [.short 0, .short 1, .short 2, .short 3],
    [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)],
    cuts.map .truncate,
    [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2],
    [size - 3, size - 35, 2 ^ 255, 2 ^ 256 - 4, 2 ^ 256 - 2, 2 ^ 256 - 1, 0, 32].map (.offset ∘ w),
    ([rows + 1, 2 ^ 251, 2 ^ 251 + 1, 2 ^ 256 - 1, rows - 1, 0].eraseDups.filter (· != rows)).map (.length ∘ w)] ++
    rowKinds

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

/-- Three outer lengths, four row lengths per transaction, three elements per
row, then the completion pattern. Each choice uses the high half of one draw
from a separate stream: the low bits of a power-of-two LCG have short periods. -/
def sequenceBounds : List Nat := [5, 5, 5] ++ List.replicate 12 4 ++ List.replicate 36 6 ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x6d616c2d6e657374)
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- A kind, a parameter and a row for each of three transactions, each the high
half of one draw from a separate stream. -/
def malformationChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofNat (seed.toNat ^^^ 0x6e6573742d6d616c)
  let mut values : Array Nat := #[]
  for bound in [9, 9, 4, 9, 9, 4, 9, 9, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Transaction `i` has `choices[i]` rows; row `r` has `choices[3 + 4i + r]`
elements, element `c` drawn by `choices[15 + 12i + 3r + c]`; the completion
pattern is `choices[51]`. Its malformation is drawn from the bank by the
kind, parameter and row choices. -/
def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let draws := malformationChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  let parities := NestedArray.parityPatterns.getD (choices.getD 51 0) [false, false, false]
  parities.zipIdx.map fun (odd, index) =>
    let values := (List.range (choices.getD index 0)).map fun row =>
      (List.range (choices.getD (3 + 4 * index + row) 0)).map fun column =>
        bank (15 + 12 * index + 3 * row + column)
    let flags := NestedArray.parityFlags odd
    let size := (Solcore.Synthesis.Stateful.NestedArrayExecution.inputBytes flags values).size
    let row := draws.getD (3 * index + 2) 0 % max values.length 1
    let kind := (malformationBank values size row).getD (draws.getD (3 * index) 0) [.none]
    ⟨"tx-" ++ toString (first + index), flags, values,
      kind.getD (draws.getD (3 * index + 1) 0 % max kind.length 1) .none⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's flags parity. -/
def completionName (tx : Transaction) : String :=
  match prescribed tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (reverts tx)

/-- Reserve the measured host wrapper before generating its independent step;
the fixed row checks and guards lie outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.MalformedNestedArray.programOverhead < nodes do
    throw "node budget is too small for the malformed-nested-array wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.MalformedNestedArray.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated malformed-nested-array plan failed full Core admission"
  let _ ← nestedPlan plan
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + guardNodes do
    throw "malformed-nested-array contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "malformed-nested-array-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("malformationChoices", toJson (Stateful.Sequence.blockChoices malformationChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map completionName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; an
accepted transaction completes with its flags parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "malformed-nested-array history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "malformed-nested-array history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (reverts tx)) do
          throw "an accepted malformed-nested-array transaction did not follow its flags parity"
    prior := current

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
        let emitted ← emit scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "malformed-nested-array history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "malformed-nested-array-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- None weighs nothing; otherwise one plus the malformation's parameters. -/
def weight : Malformation → Nat
  | .none => 0
  | .short bytes => 1 + bytes
  | .selector mask => 1 + mask
  | .truncate kept => 1 + kept
  | .trailing count pattern => 1 + count + pattern
  | .offset value => 1 + value.val
  | .length value => 1 + value.val
  | .rowOffset row value => 1 + row + value.val
  | .rowLength row value => 1 + row + value.val

def malformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + weight transaction.malformation) 0

/-- Every row and every element counts once. -/
def shapeSize (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => sum + 1 + row.length) total) 0

/-- Flags and elements all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => row.foldl (fun inner value => inner + value.val) sum)
      (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the malformation
weight, the number of rows and elements, then flags and element values. Every
axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (malformationWeight candidate < malformationWeight source ∨
      (malformationWeight candidate = malformationWeight source ∧
        (shapeSize candidate < shapeSize source ∨
        (shapeSize candidate = shapeSize source ∧ valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let _ ← (nestedPlan plan).toOption
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

private def dropLastOf (values : List (List Word)) (row : Nat) : List (List Word) :=
  values.zipIdx.map fun (cells, current) => if current == row then cells.dropLast else cells

/-- Simpler malformations of the same kind and row, from the smallest parameter up. -/
def simpler (tx : Transaction) : List Malformation :=
  let bank := (malformationBank tx.values (canonicalSize tx) ((rowOf tx.malformation).getD 0)).getD
    (malformationKinds.idxOf (kindOf tx.malformation)) []
  let ordered := bank.mergeSort fun left right => weight left ≤ weight right
  ordered.filter (weight · < weight tx.malformation)

/-- One-transaction removals first, from the last back, then step reductions.
Then, for each transaction: no malformation, simpler malformations of its kind,
removal of each row, removal of each nonempty row's last element, zeroing every
element, and flags reduced to their parity or with the revert bit cleared.
Candidates still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation := .none})]
    for malformation in simpler transaction do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation})]
    for row in List.range transaction.values.length do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with values := tx.values.eraseIdx row})]
    for (cells, row) in transaction.values.zipIdx do
      if !cells.isEmpty then
        raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
          {tx with values := dropLastOf tx.values row})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with values := tx.values.map fun cells => cells.map fun _ => Word.zero})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.MalformedNestedArray.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← emit admitted.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from the nested-array emission of the step"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the nested-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "malformed-nested-array-generated" then
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
      throw "saved origin differs from generated malformed-nested-array provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported malformed-nested-array case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.MalformedNestedArray
