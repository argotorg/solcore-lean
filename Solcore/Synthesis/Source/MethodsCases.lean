import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.MethodsEmitter
import Solcore.Synthesis.Stateful.MethodsExecution

/-! Several-methods cases retain one original host-aware Core contract with two
to four external methods, each with its own checked aggregate step over shared
slots, and an ordered history of calls. A transaction calls one recorded
method with recorded Word inputs, or sends the case's missing selector with one
Word. Each case records the methods' names, signatures, selectors, arities and
selector order. Reductions remove transactions, then methods no remaining
transaction calls, then simplify each step and the inputs. Saved outputs are
never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Methods
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan Shape minMethods maxMethods maxArity maxGuardNodes)
open Solcore.Synthesis.Stateful.MethodsExecution (Method Transaction Bindings stdRejection? selectorOf)

def caseSchema : String := "solcore-lean.semantic-methods-case.v1"
def planSchema : String := "solcore-lean.methods-plan.v1"
def profileVersion : String := "stateful-methods-v1/methods-sequence-seed-v2"
def templateVersion : String := "std-dispatch-methods-shared-slots-revert-odd-input-v1"
def corpusSchema : String := "solcore-lean.semantic-methods-corpus.v1"

/-- Inputs; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts may exceed the step budget by the methods' guards. -/
def maxProgramNodes : Nat := 512 + maxGuardNodes

private def hexDigits : List Char := "0123456789abcdef".toList

/-- `m_` and eight lowercase hexadecimal digits. -/
def validName (name : String) : Bool :=
  name.length == 10 && name.startsWith "m_" && (name.drop 2).all (hexDigits.contains ·)

def nameOf (value : Nat) : String :=
  "m_" ++ String.ofList ((List.range 8).reverse.map fun index => hexDigits.getD (value / 16 ^ index % 16) '0')

/-- The order of the method selectors, read in declaration order. -/
def selectorOrder (methods : List Method) : String :=
  let selectors := methods.map (·.selector)
  let pairs := selectors.zip (selectors.drop 1)
  if pairs.all (fun (left, right) => left < right) then "ascending"
  else if pairs.all (fun (left, right) => left > right) then "descending"
  else "mixed"

/-- Two to four methods with valid distinct names and at most two arguments;
the missing selector is a 32-bit value no method has, and no two selectors
coincide, as the compiler rejects colliding ones. -/
def validMethods (methods : List Method) (missing : Nat) : Bool :=
  let selectors := methods.map (·.selector)
  minMethods ≤ methods.length && methods.length ≤ maxMethods &&
    methods.all (fun method => validName method.name && method.arity ≤ maxArity) &&
    (methods.map (·.name)).Nodup && selectors.Nodup && missing < 2 ^ 32 && !selectors.contains missing

def validTransactions (methods : List Method) (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧
    transactions.all (fun tx => Storage.validId tx.id && tx.valid methods) = true

instance (methods : List Method) (transactions : List Transaction) :
    Decidable (validTransactions methods transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  methods : List Method
  missing : Nat
  transactions : List Transaction
  shaped : (plan.shapes == methods.map (·.shape)) = true
  named : validMethods methods missing = true
  valid : validTransactions methods transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (methods : List Method) (missing : Nat) (transactions : List Transaction) :
    Except String CheckedScenario := do
  if shaped : (plan.shapes == methods.map (·.shape)) = true then
    if named : validMethods methods missing = true then
      if valid : validTransactions methods transactions then
        if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
          return ⟨plan, methods, missing, transactions, shaped, named, valid, bounded⟩
        else throw "canonical several-methods contract exceeds its case limit"
      else throw s!"several-methods scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, each calling a declared method with its arguments or sending the missing selector with one Word"
    else throw "several-methods scenario requires two to four distinctly named methods of at most two arguments with distinct selectors and a missing selector none of them has"
  else throw "methods plan differs from the methods' selectors and arities"

def selectorText (selector : Nat) : String := Stateful.StdCalldata.selectorText selector

def prescribed (scenario : CheckedScenario) (tx : Transaction) : Option Nat :=
  stdRejection? scenario.plan.shapes
    (Solcore.Synthesis.Stateful.MethodsExecution.inputBytes scenario.methods scenario.missing tx)

def transactionJson (methods : List Method) (missing : Nat) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id),
  ("method", match tx.target with
    | some position => toJson (methods.getD position ⟨"", 0⟩).name
    | none => Json.null),
  ("selector", toJson (selectorText (Solcore.Synthesis.Stateful.MethodsExecution.sentSelector methods missing tx))),
  ("inputs", toJson (tx.inputs.map fun value => toString value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MethodsExecution.calldata methods missing tx)),
  ("stdRejection", match stdRejection? (methods.map (·.shape))
      (Solcore.Synthesis.Stateful.MethodsExecution.inputBytes methods missing tx) with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (methods : List Method) (missing : Nat) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson methods missing))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def selectorValue (text : String) : Except String Nat := do
  unless text.length == 10 && text.startsWith "0x" && (text.drop 2).all (hexDigits.contains ·) do
    throw "a selector is 0x and eight lowercase hexadecimal digits"
  return (text.drop 2).foldl (fun total digit => total * 16 + hexDigits.idxOf digit) 0

def decodeTransactions (methods : List Method) (missing : Nat) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let target ← match ← row.getObjVal? "method" with
      | .null => pure none
      | name => do
          let text ← name.getStr?
          let some position := methods.findIdx? (·.name == text) | throw "transaction names an undeclared method"
          pure (some position)
    let texts ← row.getObjValAs? (List String) "inputs"
    unless texts.length ≤ maxArity do throw "a transaction carries at most two inputs"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", target, ← texts.mapM word⟩
    unless Storage.validId transaction.id && transaction.valid methods do
      throw "invalid transaction ID or inputs for its method"
    unless row == transactionJson methods missing transaction do
      throw "transaction differs from canonical ID, method, selector, inputs, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions methods transactions do
    throw "several-methods scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) (methods : List Method) (missing : Nat) : Json := Json.mkObj [
  ("schema", toJson planSchema),
  ("methods", toJson ((methods.zip plan.steps).map fun (method, step) => Json.mkObj [
    ("name", toJson method.name), ("arity", toJson method.arity),
    ("stepProgram", Wire.encodeProgram step.program)])),
  ("missingSelector", toJson (selectorText missing))]

/-- The plan, its methods and the missing selector. -/
def checkedPlan (json : Json) : Except String (CheckedPlan × List Method × Nat) := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported several-methods plan schema"
  let rows ← json.getObjValAs? (List Json) "methods"
  unless minMethods ≤ rows.length && rows.length ≤ maxMethods do throw "a plan has two to four methods"
  let parts ← rows.mapM fun row => do
    let method : Method := ⟨← row.getObjValAs? String "name", ← row.getObjValAs? Nat "arity"⟩
    let step ← Aggregate.checkedFunction (← row.getObjVal? "stepProgram")
    pure (method, step)
  let methods := parts.map Prod.fst
  let missing ← selectorValue (← json.getObjValAs? String "missingSelector")
  unless validMethods methods missing do
    throw "plan methods need valid distinct names, at most two arguments and distinct selectors other than the missing one"
  let some plan := CheckedPlan.ofParts? (methods.map (·.shape)) (parts.map Prod.snd) |
    throw "several-methods contract failed full host-Core admission"
  unless json == planJson plan methods missing do throw "several-methods plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "several-methods contract exceeds its case limit"
  return (plan, methods, missing)

def emitted (plan : CheckedPlan) (methods : List Method) : Except String EmittedMethods :=
  (emit plan methods).mapError reprStr

def contractJson (methods : List Method) (emitted : EmittedMethods) : Json := Json.mkObj [
  ("name", toJson emitted.contractName),
  ("methods", toJson (methods.map fun method => Json.mkObj [
    ("name", toJson method.name), ("signature", toJson method.signature),
    ("selector", toJson (selectorText method.selector)), ("arity", toJson method.arity)])),
  ("selectorOrder", toJson (selectorOrder methods)),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedMethods) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("methodsPlan", planJson scenario.plan scenario.methods scenario.missing),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.methods scenario.missing scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MethodsExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.ContractMethods.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson (scenario.plan.steps.flatMap (·.features)))]),
    ("contract", contractJson scenario.methods emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let source ← emitted scenario.plan scenario.methods
  return makeCase scenario source origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic several-methods case schema"
  let (plan, methods, missing) ← checkedPlan (← json.getObjVal? "methodsPlan")
  let transactions ← decodeTransactions methods missing (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical several-methods plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MethodsExecution.slotsJson do
    throw "observed slots must be zero through five"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan methods missing transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MethodsExecution.observe scenario.plan scenario.methods scenario.missing
    scenario.transactions bindings fuel

/-- The wrapping sum of a transaction's inputs; odd sums revert. -/
def inputSum (tx : Transaction) : Nat := tx.inputs.foldl (fun total value => (total + value.val) % 2 ^ 256) 0

def reverts (tx : Transaction) : Bool := inputSum tx % 2 == 1

/-- The method count, then each of four methods' name and arity, then the
missing method's name; each the high half of one draw from one stream of the
scenario seed. The stream starts at SplitMix64's finalizer of the seed xor its
domain, so that consecutive seeds' choices do not step by a fixed residue. -/
def shapeChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d6574686f64732d))
  let mut values : Array Nat := #[]
  for bound in [3] ++ (List.replicate maxMethods [2 ^ 32, 3]).flatten ++ [2 ^ 32] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The methods and the missing selector a scenario seed draws. -/
def drawnShape (seed : Seed) : List Method × Nat :=
  let choices := shapeChoices seed
  let count := minMethods + choices.getD 0 0
  let methods := (List.range count).map fun index =>
    (⟨nameOf (choices.getD (1 + 2 * index) 0), choices.getD (2 + 2 * index) 0⟩ : Method)
  let missing := (⟨nameOf (choices.getD (1 + 2 * maxMethods) 0), 1⟩ : Method).selector
  (methods, missing)

/-- Eight candidate step seeds for method `position`, each the finalizer of one
draw from the method's own stream; its step comes from the first that fits the
budget. The stream starts at the finalizer of the seed xor the domain
`"methstep" + position`, which no position below four carries out of its last
byte, so it meets neither the shape nor the sequence domain, and the
candidates' helper counts and templates are not affine in the seed. -/
def stepSeeds (seed : Seed) (position : Nat) : List Seed := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ (0x6d65746873746570 + position.toUInt64)))
  let mut values : Array Seed := #[]
  for _ in List.range 8 do
    let (value, next) := GeneratorV2.draw state
    values := values.push (Seed.ofUInt64 value)
    state := next
  return values.toList

/-- A target below `2n + 1` for `n` methods and two inputs for each of three
transactions, each the high half of one draw from a separate stream. The stream
starts at SplitMix64's finalizer of the seed xor its domain, so that consecutive
seeds' choices do not step by a fixed residue. -/
def sequenceChoices (count : Nat) (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d6574686f642d74))
  let mut values : Array Nat := #[]
  for bound in List.replicate 3 [2 * count + 1, 6, 6] |>.flatten do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Transaction `i` targets the missing selector when its target choice is
`2n`, otherwise method `choice % n`, so each method is called two times in
`2n + 1` and the missing selector once, with that method's arguments, or one
Word for the missing selector, from the boundary bank. -/
def blockTransactions (methods : List Method) (seed : Seed) (first : Nat) : List Transaction :=
  let count := methods.length
  let choices := sequenceChoices count seed
  (List.range 3).map fun index =>
    let choice := choices.getD (3 * index) 0
    let target := if choice < 2 * count then some (choice % count) else none
    let arity := match target with
      | some position => (methods.getD position ⟨"", 0⟩).arity
      | none => 1
    ⟨"tx-" ++ toString (first + index), target,
      (List.range arity).map fun argument => boundaryInputs.getD (choices.getD (3 * index + 1 + argument) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (methods : List Method) (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks (blockTransactions methods) seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's input parity. -/
def completionName (scenario : CheckedScenario) (tx : Transaction) : String :=
  match prescribed scenario tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (reverts tx)

/-- The dispatch shell lies inside the node budget and the methods' guards
outside it; the methods share the rest equally. Each step comes from the first
of its method's candidate seeds whose template fits that share, under the
case's one swarm mask. The complete contract is remeasured as the final budget
authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.ContractMethods.programOverhead < nodes do
    throw "node budget is too small for the several-methods wrapper or exceeds 512"
  let (methods, missing) := drawnShape seed
  unless validMethods methods missing do throw "drawn method selectors collide"
  let budget := (nodes - Solcore.Synthesis.Core.ContractMethods.programOverhead) / methods.length
  let mask := revision.caseMask seed
  let mut steps : List Aggregates.CheckedDAG := []
  let mut stepOrigins : Array Json := #[]
  for position in List.range methods.length do
    let mut chosen : Option (Aggregates.CheckedDAG × Json) := none
    for (candidate, attempt) in (stepSeeds seed position).zipIdx do
      if chosen.isNone then
        if let .ok (step, stepOrigin) := Aggregate.generatedFunction candidate budget revision (some mask) then
          chosen := some (step, stepOrigin.setObjVal! "attempt" (toJson attempt))
    let some (step, stepOrigin) := chosen | throw "no candidate step seed fits the method's budget"
    steps := steps ++ [step]
    stepOrigins := stepOrigins.push stepOrigin
  let some plan := CheckedPlan.ofParts? (methods.map (·.shape)) steps |
    throw "generated several-methods plan failed full Core admission"
  let scenario ← checkedScenario plan methods missing (generatedTransactions methods seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + Solcore.Synthesis.Core.ContractMethods.guardNodes plan.shapes do
    throw "several-methods contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "methods-generated"), ("seed", toJson (toString seed.toNat)),
    ("maxProgramNodes", toJson nodes), ("shapeChoices", toJson (shapeChoices seed)),
    ("stepOrigins", .arr stepOrigins),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices (sequenceChoices methods.length) seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map (completionName scenario)))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; a call
completes with its input parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  for step in scenario.plan.steps do
    Aggregate.inputSensitive step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "several-methods history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "several-methods history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed scenario tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (reverts tx)) do
          throw "a several-methods call did not follow its input parity"
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
        let source ← emitted scenario.plan scenario.methods
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), source)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "several-methods history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "methods-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, source) =>
          cases := cases.push (makeCase scenario source origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total tx => tx.inputs.foldl (fun sum value => sum + value.val) total) 0

/-- Transaction count, method count, complete program size/literals, then the
inputs. Every axis is a natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.methods.length < source.methods.length ∨
    (candidate.methods.length = source.methods.length ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        inputWeight candidate < inputWeight source)))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

/-- Each remaining method keeps its name and its step's helper count and
binding inventory. -/
def keepsSteps (candidate source : CheckedScenario) : Bool :=
  (candidate.methods.zip candidate.plan.steps).all fun (method, step) =>
    match source.methods.findIdx? (·.name == method.name) with
    | some position =>
        match source.plan.steps[position]? with
        | some original => step.helpers.length == original.helpers.length &&
            Aggregate.bindingInventory step == Aggregate.bindingInventory original
        | none => false
    | none => false

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameSteps : keepsSteps candidate source = true
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (methods : List Method) (steps : List Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? (methods.map (·.shape)) steps
  let candidate ← (checkedScenario plan methods source.missing transactions).toOption
  if same : keepsSteps candidate source = true then
    if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
      if strict : StrictlySmaller candidate source then some ⟨candidate, same, ids, strict⟩
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Without method `removed`, later positions move down by one. -/
private def retarget (removed : Nat) (tx : Transaction) : Transaction :=
  {tx with target := tx.target.map fun position => if position > removed then position - 1 else position}

/-- One-transaction removals first, from the last back; then the removal of
each method no transaction calls, from the last back; then each method's step
reductions; then each input replaced by zero or a smaller bank value.
Candidates still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let methods := source.methods
  let steps := source.plan.steps
  let mut raw : List (List Method × List Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(methods, steps,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for position in (List.range methods.length).reverse do
    if source.transactions.all (·.target != some position) then
      raw := raw ++ [(methods.eraseIdx position, steps.eraseIdx position, source.transactions.map (retarget position))]
  for (step, position) in steps.zipIdx do
    for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
      raw := raw ++ [(methods, steps.set position reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for (value, argument) in transaction.inputs.zipIdx do
      for smaller in boundaryInputs do
        if smaller.val < value.val then
          raw := raw ++ [(methods, steps, replaceAt source.transactions index fun tx =>
            {tx with inputs := tx.inputs.set argument smaller})]
  let mut seen : List String := []
  let mut result := []
  for (methods, steps, transactions) in raw do
    if let some reduced := sealReduction source methods steps transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.methods reduced.candidate.missing
          reduced.candidate.transactions)]).compress
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
      ("functionVersion", Solcore.Synthesis.Core.ContractMethods.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let source ← emitted admitted.plan admitted.methods
  unless (← json.getObjValAs? String "source") = source.source do
    throw "saved source differs from the several-methods emission"
  unless (← json.getObjVal? "contract") == contractJson admitted.methods source do
    throw "saved contract metadata differs from the several-methods wrapper"
  unless (← provenance.getObjVal? "features") == toJson (admitted.plan.steps.flatMap (·.features)) do
    throw "saved features differ from the checked steps"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "methods-generated" then
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
      throw "saved origin differs from generated several-methods provenance"
    unless planJson expected.plan expected.methods expected.missing == planJson admitted.plan admitted.methods admitted.missing &&
        transactionsJson expected.methods expected.missing expected.transactions ==
          transactionsJson admitted.methods admitted.missing admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let (parentPlan, parentMethods, parentMissing) ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentMethods parentMissing (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentMethods parentMissing parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do
      throw "reduction parent program differs from its plan"
    unless admitted.missing == parent.missing &&
        (sealReduction parent admitted.methods admitted.plan.steps admitted.transactions).isSome do
      throw "reduction does not keep the methods' steps and IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"),
        ("parentPlan", planJson parent.plan parent.methods parent.missing),
        ("parentProgram", Wire.encodeProgram parent.program),
        ("parentTransactions", transactionsJson parent.methods parent.missing parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported several-methods case origin"
  return makeCase admitted source origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"),
    ("parentPlan", planJson source.plan source.methods source.missing),
    ("parentProgram", Wire.encodeProgram source.program),
    ("parentTransactions", transactionsJson source.methods source.missing source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.Methods
