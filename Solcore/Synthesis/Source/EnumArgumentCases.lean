import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.EnumArgumentEmitter
import Solcore.Synthesis.Stateful.EnumArgumentExecution

/-! Enum-argument cases retain one original host-aware Core contract, its enum's
constructors, and an ordered history of transactions, each a constructor with
its field Words or `bytes` length and one malformation of its calldata.
Reductions remove transactions, simplify malformations, shorten lengths, drop
unused constructors, narrow fields, reduce the step and simplify the Words.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EnumArgument
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EnumArgument (CheckedPlan Constructor Payload Shape)
open Solcore.Synthesis.Stateful.EnumArgumentExecution (Transaction Malformation Bindings maxLength carriesBytes
  inputBytes stdRejection? calldata slotsJson hasUnused paddingCount canonicalSize bodyStart payloadStart stdDecode)

private def chosenConstructor (shape : Shape) (tx : Transaction) : Constructor :=
  Solcore.Synthesis.Stateful.EnumArgumentExecution.constructor shape tx

def caseSchema : String := "solcore-lean.semantic-enum-argument-case.v1"
def planSchema : String := "solcore-lean.enum-argument-plan.v1"
def profileVersion : String := "stateful-enum-arguments-v1/enum-argument-sequence-seed-v1"
def templateVersion : String := "std-enum-decode-index-words-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-enum-argument-corpus.v1"

/-- Flags values and field Words; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Lengths drawn with probability one half: empty, the Word boundaries and the
bound. -/
def lengthBank : List Nat := [0, 1, 31, 32, 33, 63, 64]

/-- The largest decoder of a valid shape, four constructors of which two carry
`bytes` and two Words; the tests check it against every shape class. -/
def maxDecoderNodes : Nat := 500

/-- Complete contracts may exceed the step budget by their shape's decoder. -/
def maxProgramNodes : Nat := 512 + maxDecoderNodes

/-- A transaction encodes an existing constructor; only a `bytes` constructor
keeps a length, of at most 64 bytes; its malformation applies, and its calldata
stays within one KiB. -/
def admits (shape : Shape) (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.choice < shape.constructors.length &&
    tx.length ≤ maxLength && (carriesBytes shape tx || tx.length == 0) &&
    tx.malformation.valid shape tx &&
    (inputBytes shape tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (shape : Shape) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (admits shape) = true

instance (shape : Shape) (transactions : List Transaction) : Decidable (validTransactions shape transactions) := by
  unfold validTransactions
  infer_instance

/-- The step's budget is at most 512 nodes; the shape's decoder lies outside it. -/
def contractBound (plan : CheckedPlan) : Nat := 512 + EnumArgument.decoderNodes plan.shape

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions plan.shape transactions
  bounded : Wire.programNodes plan.program ≤ contractBound plan

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

private def transactionRule : String :=
  s!"enum-argument scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, a constructor of the shape, a length of at most {maxLength} that only a bytes constructor's transaction may set, a malformation that applies to it, and calldata of at most 1 KiB"

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions plan.shape transactions then
    if bounded : Wire.programNodes plan.program ≤ contractBound plan then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical enum-argument contract exceeds its case limit"
  else throw transactionRule

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "tag", "retag", "offset", "aliased", "unused",
    "tail", "length", "padding"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .tag _ => "tag"
  | .retag _ => "retag"
  | .offset _ => "offset"
  | .aliased _ => "aliased"
  | .unused _ => "unused"
  | .tail _ => "tail"
  | .length _ => "length"
  | .padding _ => "padding"

abbrev patternNames := Stateful.StdCalldata.patternNames
def paddingNames : List String := ["ones", "ramp", "last-byte"]

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .tag value => Json.mkObj [("kind", toJson "tag"), ("value", toJson (toString value.val))]
  | .retag index => Json.mkObj [("kind", toJson "retag"), ("constructor", toJson index)]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .aliased index => Json.mkObj [("kind", toJson "aliased"), ("constructor", toJson index)]
  | .unused value => Json.mkObj [("kind", toJson "unused"), ("value", toJson (toString value.val))]
  | .tail value => Json.mkObj [("kind", toJson "tail"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .padding pattern => Json.mkObj [("kind", toJson "padding"),
      ("pattern", toJson (paddingNames.getD pattern "last-byte"))]

/-- std's revert data as text: an error selector, `0x` for an unknown tag, or
null when the body runs. -/
def prescribed (shape : Shape) (tx : Transaction) : Option String :=
  (stdRejection? shape tx).map Solcore.ContractRuntime.encodeBytesText

def transactionJson (shape : Shape) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("choice", toJson tx.choice),
  ("first", toJson (toString tx.first.val)), ("second", toJson (toString tx.second.val)),
  ("length", toJson tx.length), ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (calldata shape tx)),
  ("stdRejection", match prescribed shape tx with
    | some data => toJson data
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (shape : Shape) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson shape))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value < 2 ^ 32 do throw s!"malformation {key} is out of range"
  return value

private def nameIndex (names : List String) (json : Json) (key : String) : Except String Nat := do
  let name ← json.getObjValAs? String key
  match names.idxOf? name with
  | some index => return index
  | none => throw s!"unknown malformation {key}"

def decodeMalformation (json : Json) : Except String Malformation := do
  match ← json.getObjValAs? String "kind" with
  | "none" => return .none
  | "short" => return .short (← natural json "bytes")
  | "selector" => return .selector (← (← word (← json.getObjValAs? String "mask")).val |> pure)
  | "truncate" => return .truncate (← natural json "kept")
  | "trailing" => return .trailing (← natural json "count") (← nameIndex patternNames json "pattern")
  | "tag" => return .tag (← word (← json.getObjValAs? String "value"))
  | "retag" => return .retag (← natural json "constructor")
  | "offset" => return .offset (← word (← json.getObjValAs? String "value"))
  | "aliased" => return .aliased (← natural json "constructor")
  | "unused" => return .unused (← word (← json.getObjValAs? String "value"))
  | "tail" => return .tail (← word (← json.getObjValAs? String "value"))
  | "length" => return .length (← word (← json.getObjValAs? String "value"))
  | "padding" => return .padding (← nameIndex paddingNames json "pattern")
  | _ => throw "unknown malformation kind"

def decodeTransactions (shape : Shape) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← natural row "choice",
      ← word (← row.getObjValAs? String "first"), ← word (← row.getObjValAs? String "second"),
      ← natural row "length", ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransactions shape [transaction] do throw transactionRule
    unless row == transactionJson shape transaction do
      throw "transaction differs from canonical ID, flags, choice, Words, length, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions shape transactions do throw transactionRule
  return transactions

/-- A constructor's declared field types: none, `uint256`, two of them, the
struct or `bytes`. -/
def fieldsName : Payload → String
  | .noWords => ""
  | .oneWord => "uint256"
  | .twoWords => "uint256,uint256"
  | .pair => structName
  | .bytes => "bytes"

def constructorJson (constructor : Constructor) : Json := Json.mkObj [
  ("name", toJson constructor.name), ("fields", toJson (fieldsName constructor.payload))]

private def payloadOf? (fields : String) : Option Payload :=
  [Payload.noWords, .oneWord, .twoWords, .pair, .bytes].find? (fieldsName · == fields)

/-- The constructors of a list of two or more, in order. -/
def Shape.ofList? : List Constructor → Option Shape
  | first :: second :: rest => some ⟨first, second, rest⟩
  | _ => none

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("constructors", toJson (plan.shape.constructors.map constructorJson)),
  ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported enum-argument plan schema"
  let rows ← (← json.getObjVal? "constructors").getArr?
  unless rows.size ≤ EnumArgument.maxConstructors do throw "an enum has at most four constructors"
  let constructors ← rows.toList.mapM fun row => do
    let some payload := payloadOf? (← row.getObjValAs? String "fields") | throw "unsupported constructor fields"
    return ({name := ← row.getObjValAs? String "name", payload} : Constructor)
  let some shape := Shape.ofList? constructors | throw "an enum needs at least two constructors"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofParts? step shape
    | throw "enum-argument plan needs two to four constructors with distinct bank names, at most two with bytes, and full host-Core admission"
  unless json == planJson plan do throw "enum-argument plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ contractBound plan do throw "enum-argument contract exceeds its case limit"
  return plan

def contractJson (shape : Shape) (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson (selectorText shape)),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("enumArgumentPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.plan.shape scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson EnumArgument.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson scenario.plan.shape emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic enum-argument case schema"
  let plan ← checkedPlan (← json.getObjVal? "enumArgumentPlan")
  let transactions ← decodeTransactions plan.shape (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical enum-argument plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.EnumArgumentExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- SplitMix64's finalizer: the generator's draws are affine in its start, so
consecutive seeds would otherwise start streams whose draws follow each other. -/
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

/-- The constructor count, the `bytes` count, four other fields, two `bytes`
positions and four name indices into the shrinking bank. -/
def shapeBounds : List Nat := [3, 4, 4, 4, 4, 4, 4, 4, 8, 7, 6, 5]

def shapeChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172677368617065 shapeBounds

/-- Names drawn from the bank without repetition: each index picks among the
names still left. -/
private def drawNames (indices : List Nat) : List String := Id.run do
  let mut left := EnumArgument.nameBank
  let mut names : Array String := #[]
  for index in indices do
    names := names.push (left.getD index "")
    left := left.eraseIdx index
  return names.toList

/-- Two to four constructors; none carries `bytes` for a `bytes` draw below 2,
otherwise one or two do, at distinct positions. The other fields are none, one
Word, two Words or the struct. -/
def generatedShape (seed : Seed) : Shape :=
  let choices := shapeChoices seed
  let count := 2 + choices.getD 0 0
  let bytesCount := choices.getD 1 0 - 1
  let firstBytes := choices.getD 6 0 % count
  let secondBytes := (firstBytes + 1 + choices.getD 7 0 % (count - 1)) % count
  let payloads := (List.range count).map fun index =>
    if (bytesCount ≥ 1 && index == firstBytes) || (bytesCount ≥ 2 && index == secondBytes) then
      Payload.bytes
    else [Payload.noWords, .oneWord, .twoWords, .pair].getD (choices.getD (2 + index) 0) .noWords
  let names := drawNames ((choices.drop 8).take count)
  let constructors := (names.zip payloads).map fun (name, payload) => ({name, payload} : Constructor)
  (Shape.ofList? constructors).getD ⟨⟨"Idle", .noWords⟩, ⟨"Ready", .noWords⟩, []⟩

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The kinds that apply to a transaction, in catalog order. -/
def applicableKinds (shape : Shape) (tx : Transaction) : List String :=
  ["short", "selector", "truncate", "trailing", "tag", "retag"] ++
    (if shape.dynamic then ["offset", "aliased"] else []) ++
    (if hasUnused shape tx then ["unused"] else []) ++
    (if carriesBytes shape tx then ["tail", "length"] else []) ++
    (if carriesBytes shape tx && paddingCount tx.length != 0 then ["padding"] else [])

/-- The generation bank of one kind for a transaction, without the entries
that do not apply to it. -/
def malformationBank (shape : Shape) (tx : Transaction) (kind : String) : List Malformation :=
  let size := canonicalSize shape tx
  let start := bodyStart shape
  let head := shape.bodyHead
  let data := payloadStart shape
  let tag := EnumArgument.tag (chosenConstructor shape tx)
  let others := (List.range shape.constructors.length).filter (· != tx.choice)
  let bank : List Malformation := match kind with
    | "short" => [.short 0, .short 1, .short 2, .short 3]
    | "selector" => [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)]
    | "truncate" =>
        let cuts := if shape.dynamic then
            [4, 36, 67, 68, 99, 100, 131, 132, 163, 164, start + head - 1, start + head, start + head + 31] ++
              (if carriesBytes shape tx && tx.length > 0 then [data + tx.length - 1] else []) ++
              (if carriesBytes shape tx && paddingCount tx.length != 0 then
                [data + tx.length] else []) ++ [size - 1]
          else [4, 35, 36, 67, size - 32, size - 1]
        (cuts.eraseDups.filter fun kept => 4 ≤ kept && kept < size).map .truncate
    | "trailing" => [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2]
    | "tag" =>
        [w 0, tag + w 1, tag ^^^ w (2 ^ 255), w (2 ^ 256 - 1),
          EnumArgument.tag ⟨(chosenConstructor shape tx).name ++ "(uint256,bytes)", .noWords⟩].eraseDups.map .tag
    | "retag" => others.map .retag
    | "offset" => ([size - 3, size - 4, size - 35, 2 ^ 255, 2 ^ 256 - 4, 2 ^ 256 - 1, 0, 16, 32, 96].map w).eraseDups.map .offset
    | "aliased" => (List.range shape.constructors.length).map .aliased
    | "unused" => [w 1, w (2 ^ 255), w (2 ^ 256 - 1)].map .unused
    | "tail" => ([size - start + 1, size - start, size - start - 31, 0, 32, 2 ^ 255, 2 ^ 256 - 1].map w).eraseDups.map .tail
    | "length" =>
        let fits := size - data
        ([tx.length + 1, fits, fits + 1, EnumArgument.maxPayloadLength + 1, 2 ^ 256 - 1, 2 ^ 255,
          tx.length - 1, 0].map w).eraseDups.map .length
    | "padding" => [.padding 0, .padding 1, .padding 2]
    | _ => []
  bank.filter (·.valid shape tx)

/-- Three flags and the completion pattern, then per transaction a choice, two
field Words, a length selector, a uniform length, whether it is malformed, a
kind and a bank entry. The last two bounds divide by every count up to 16. -/
def sequenceBounds : List Nat :=
  [6, 6, 6, 4] ++ (List.range 3).flatMap fun _ => [12, 6, 6, 14, 65, 3, 720720, 720720]

def sequenceChoices (seed : Seed) : List Nat := boundedDraws seed 0x6172677365716e63 sequenceBounds

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 3 0) [false, false, false]

/-- A selector below seven picks that entry of the length bank; otherwise the
uniform draw from 0 to 64 is the length. -/
def generatedLength (selector uniform : Nat) : Nat :=
  if selector < lengthBank.length then lengthBank.getD selector 0 else uniform

/-- A choice draw below 12 is uniform below any count from 2 to 4; only a
`bytes` constructor's transaction keeps its length. A third of the transactions
are canonical; the others draw a kind uniformly from those that apply, then an
entry of its bank. -/
def blockTransactions (shape : Shape) (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD index Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    let draw := fun (offset : Nat) => choices.getD (4 + 8 * index + offset) 0
    let choice := draw 0 % shape.constructors.length
    let base : Transaction := ⟨"tx-" ++ toString (first + index),
      parityInput odd (bank (choices.getD index 0)), choice, bank (draw 1), bank (draw 2), 0, .none⟩
    let base := if carriesBytes shape base then {base with length := generatedLength (draw 3) (draw 4)} else base
    if draw 5 == 0 then base
    else
      let kinds := applicableKinds shape base
      let entries := malformationBank shape base (kinds.getD (draw 6 % max kinds.length 1) "none")
      {base with malformation := entries.getD (draw 7 % max entries.length 1) .none}

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (shape : Shape) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions shape) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: std's rejection, or the decoded flags' parity. -/
def completionName (shape : Shape) (tx : Transaction) : String :=
  match stdDecode shape (inputBytes shape tx) with
  | .error data => "rejected:" ++ Solcore.ContractRuntime.encodeBytesText data
  | .ok decoded => statusName (decoded.flags.val % 2 == 1)

/-- Whether the decoded flags or a rejection make a transaction revert. -/
def reverts (shape : Shape) (tx : Transaction) : Bool := completionName shape tx != "returned"

/-- The fixed wrapper lies inside the budget and the shape's decoder outside
it; the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  let shape := generatedShape seed
  let overhead := EnumArgument.programOverhead shape
  unless nodes ≤ 512 && overhead < nodes do
    throw "node budget is too small for the enum-argument wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - overhead) revision
  let some plan := CheckedPlan.ofParts? step shape | throw "generated enum-argument plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions shape seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + EnumArgument.decoderNodes shape do
    throw "enum-argument contract exceeds its requested node budget and decoder"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "enum-argument-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin), ("shapeChoices", toJson (shapeChoices seed)),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map (completionName shape)))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "enum-argument history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map rowStatus == scenario.transactions.map (fun tx =>
      some (if reverts scenario.plan.shape tx then "reverted" else "returned")) do
    throw "enum-argument history did not follow its prescribed outcomes"

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
            error == "enum-argument history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "enum-argument-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def payloadWeight : Payload → Nat
  | .noWords => 0
  | .oneWord => 1
  | .twoWords => 2
  | .pair => 3
  | .bytes => 4

/-- One per constructor and its fields' weight. -/
def shapeWeight (shape : Shape) : Nat :=
  shape.constructors.foldl (fun total constructor => total + 1 + payloadWeight constructor.payload) 0

/-- Nothing for no malformation, otherwise one plus its position in its kind's
bank, or one plus the bank's size outside it. -/
def malformationWeight (shape : Shape) (tx : Transaction) : Nat :=
  match tx.malformation with
  | .none => 0
  | malformation =>
      let bank := malformationBank shape tx (kindOf malformation)
      1 + (bank.idxOf? malformation).getD bank.length

def totalMalformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + malformationWeight scenario.plan.shape tx) 0

def totalLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.length) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => total + tx.first.val + tx.second.val + tx.flags.val) 0

/-- Transaction count, the shape's weight, the malformations' weight, the total
length, complete program size/literals, then the field Words and flags. Every
axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (shapeWeight candidate.plan.shape < shapeWeight source.plan.shape ∨
    (shapeWeight candidate.plan.shape = shapeWeight source.plan.shape ∧
      (totalMalformationWeight candidate < totalMalformationWeight source ∨
      (totalMalformationWeight candidate = totalMalformationWeight source ∧
        (totalLength candidate < totalLength source ∨
        (totalLength candidate = totalLength source ∧
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

/-- The constructor indices a transaction names: its choice, and a retag's or an
alias's constructor. -/
def namedConstructors (tx : Transaction) : List Nat :=
  tx.choice :: match tx.malformation with
    | .retag index | .aliased index => [index]
    | _ => []

/-- A shape change's transactions: a malformation that no longer applies
becomes none. -/
private def reanchor (shape : Shape) (transactions : List Transaction) : List Transaction :=
  transactions.map fun tx => if tx.malformation.valid shape tx then tx else {tx with malformation := .none}

private def moveDown (index value : Nat) : Nat := if value > index then value - 1 else value

/-- The shape without constructor `index`, and the indices above it moved down. -/
private def dropConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let smaller ← Shape.ofList? (shape.constructors.eraseIdx index)
  return (smaller, reanchor smaller (transactions.map fun tx =>
    {tx with choice := moveDown index tx.choice, malformation := match tx.malformation with
      | .retag other => .retag (moveDown index other)
      | .aliased other => .aliased (moveDown index other)
      | malformation => malformation}))

/-- The next narrower fields: the struct to two Words, two Words to one, one
Word to none and `bytes` to none. -/
private def narrower : Payload → Option Payload
  | .pair => some .twoWords
  | .twoWords => some .oneWord
  | .oneWord => some .noWords
  | .bytes => some .noWords
  | .noWords => none

/-- Constructor `index` with narrower fields; a `bytes` constructor's
transactions lose their lengths. -/
private def narrowConstructor (shape : Shape) (transactions : List Transaction) (index : Nat) :
    Option (Shape × List Transaction) := do
  let constructor ← shape.constructors[index]?
  let payload ← narrower constructor.payload
  let smaller ← Shape.ofList? (shape.constructors.set index {constructor with payload})
  return (smaller, reanchor smaller (transactions.map fun tx =>
    if tx.choice == index then {tx with length := 0} else tx))

/-- One-transaction removals, simpler malformations, shorter lengths, dropped
and narrowed constructors, step reductions, then per transaction zero field
Words and the flags' parity bit. Candidates still need execution to establish
that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let shape := source.plan.shape
  let mut raw : List (Aggregates.CheckedDAG × Shape × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, shape,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for (transaction, index) in source.transactions.zipIdx do
    let bank := malformationBank shape transaction (kindOf transaction.malformation)
    let earlier := match bank.idxOf? transaction.malformation with
      | some position => bank.take position
      | none => bank
    for simpler in Malformation.none :: earlier do
      if simpler != transaction.malformation then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with malformation := simpler})]
  -- A shorter length, empty or halved, keeps every other part of its transaction.
  for (transaction, index) in source.transactions.zipIdx do
    for shorter in [0, transaction.length / 2] do
      if shorter < transaction.length then
        raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
          {tx with length := shorter})]
  -- A constructor no transaction names can go while two others remain.
  for index in List.range shape.constructors.length do
    unless source.transactions.any (fun tx => (namedConstructors tx).contains index) do
      if let some (smaller, transactions) := dropConstructor shape source.transactions index then
        raw := raw ++ [(source.plan.step, smaller, transactions)]
  for index in List.range shape.constructors.length do
    if let some (smaller, transactions) := narrowConstructor shape source.transactions index then
      raw := raw ++ [(source.plan.step, smaller, transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, shape, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with first := Word.zero, second := Word.zero})]
    raw := raw ++ [(source.plan.step, shape, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
  let mut seen : List String := []
  let mut result := []
  for (step, shape, transactions) in raw do
    if let some reduced := sealReduction source step shape transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.plan.shape reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.plan.shape parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", EnumArgument.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from enum-argument plan emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.plan.shape emitted do
    throw "saved contract metadata differs from enum-argument wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "enum-argument-generated" then
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
      throw "saved origin differs from generated enum-argument provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.plan.shape expected.transactions ==
          transactionsJson admitted.plan.shape admitted.transactions do
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
  else throw "unsupported enum-argument case origin"
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

end Solcore.Synthesis.Source.EnumArgument
