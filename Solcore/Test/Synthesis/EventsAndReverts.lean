import Solcore.Synthesis.Internal.AdtStorage
import Solcore.Synthesis.Internal.RevertData

/-!
# Event and revert profile tests

Event logs and revert data.
-/

section
-- leanmerge: from Solcore.Test.SourceEventLogCases
/-! Event-log case regressions: exact replay, bounded generation from an
independent site and sequence stream, canonical transaction/site boundaries,
static log shapes and typed scenario reductions over steps, sites,
transactions, inputs and flags. Expected values here are test goldens only;
emitted cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceEventLogCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site validSites)
open Solcore.Synthesis.Stateful.EventLogExecution (Transaction Bindings)

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
private def rows (value : Json) (name : String := "transactions") : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) name)
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩⟩

private def makePlan (body : Wire.Expr) (sites : List Site) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] entry |
    throw (IO.userError "log fixture failed step admission")
  let some plan := CheckedPlan.ofParts? graph sites | throw (IO.userError "log wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, input), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat)) : IO EventLog.CheckedScenario :=
  get (EventLog.checkedScenario plan (transactions values))
private def imported (value : EventLog.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (EventLog.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

/-- Logs of every row with the emitter address removed. -/
private def withoutAddresses (history : Json) : IO (Array Json) := do
  (← rows history).mapM fun row => do
    let logs ← get (row.getObjValAs? (Array Json) "logs")
    return Solcore.Synthesis.Stateful.AccountStorage.unbound (row.setObjVal! "logs" (toJson (logs.map fun log => log.setObjVal! "address" Json.null)))

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0) [⟨1, 2, 1⟩, ⟨3, 4, 0⟩]
  let value ← scenario identity [(2, 5), (11, 1), (8, 2 ^ 255)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1"] : List String)) "log case changed its observed slots"
  ensure ((← field saved "logPlan") == EventLog.planJson identity) "log case lost its site plan"
  ensure ((← get (EventLog.replayCase saved 10000)) == saved) "imported log case did not replay"
  ensure ((← get (EventLog.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "log replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(15, 1), (0, 3)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "flags or inputs were substituted into source or Core code"
  let observed := EventLog.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "log scenario did not follow its flags parities"
  let shapes ← (← rows observed).mapM fun row => do
    let logs ← get (row.getObjValAs? (Array Json) "logs")
    logs.mapM fun log => do
      let topics ← get (log.getObjValAs? (List String) "topics")
      let address ← string log "address"
      ensure (address == "101") "log emitter is not the bound contract"
      return (topics.length, ((← string log "data").length - 2) / 2)
  ensure (shapes == #[#[(2, 32)], #[], #[(4, 0)]] &&
    shapes.toList.map Array.toList == value.transactions.map (EventLog.expectedShapes identity))
    "observed logs differ from the static site shapes"
  ensure ((value.transactions.map fun tx => (EventLog.guardedSites identity tx).length) == [1, 2, 1] &&
    (value.transactions.map EventLog.reverts) == [false, true, false])
    "guarded sites or completions changed"
  ensure ((← withoutAddresses (EventLog.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)) ==
      (← withoutAddresses observed))
    "address-independent log values changed with bindings"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let choices := EventLog.sequenceChoices (Seed.ofNat seed)
    let bounds := [3, 5, 3, 5, 3, 5, 3, 3, 6, 6, 6, 8, 8, 8, 2, 2, 2, 4]
    ensure (choices.length == bounds.length && (choices.zip bounds).all fun (value, bound) => value < bound)
      "sequence choices escaped their banks"
    let sites := EventLog.generatedSites (Seed.ofNat seed)
    ensure (validSites sites && 1 ≤ sites.length) "generated sites are invalid or empty"
    match EventLog.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3 && value.plan.sites == sites)
          "log recipe lost node/transaction/helper/site bounds"
        ensure (value.transactions.all fun tx => EventLog.boundaryInputs.contains tx.input)
          "generated input escaped its bank"
        ensure ((value.transactions.map EventLog.reverts) == EventLog.generatedParities (Seed.ofNat seed))
          "generated flags lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (EventLog.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (EventLog.generatedScenario (Seed.ofNat 0)
    (EventLog.programOverhead (EventLog.generatedSites (Seed.ofNat 0)))) "undersized node budget accepted"
  let corpus := EventLog.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == EventLog.generateCases (Seed.ofNat 0) 384 4 512 10000) "log generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "log count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (EventLog.replayCase saved 10000)) == saved) "generated log provenance did not replay"
    let low ← get (EventLog.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := EventLog.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "log generation resource exhaustion was not distinguished"
  ensure ((← rows (EventLog.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (EventLog.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (EventLog.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "log generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "02"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "6"), ("input", toJson "05"), ("input", toJson "7"),
      ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (EventLog.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical log transaction accepted"
  rejected (EventLog.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (EventLog.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (EventLog.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0"] : List String)), ("observedSlots", toJson (["1", "0"] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("logPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (EventLog.caseProgram (saved.setObjVal! name bad)) "invalid log case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "framingVersion", "templateVersion",
      "stepProfileVersion", "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (EventLog.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered log provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (EventLog.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated log recipe accepted"
  let plan ← field saved "logPlan"
  let sites ← get (plan.getObjValAs? (Array Json) "sites")
  rejected (EventLog.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical log plan accepted"
  rejected (EventLog.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.keyed-storage-plan.v1")))
    "keyed plan schema accepted as a log plan"
  for bad in [sites.set! 0 (sites[0]!.setObjVal! "extra" Json.null), sites.set! 0 (sites[0]!.setObjVal! "guard" (toJson (0 : Nat))),
      sites.set! 0 (sites[0]!.setObjVal! "topics" (toJson (5 : Nat))), sites.set! 0 (sites[0]!.setObjVal! "dataWords" (toJson (3 : Nat))),
      sites.reverse, sites.push sites[0]!, (sites ++ sites)] do
    rejected (EventLog.checkedPlan (plan.setObjVal! "sites" (toJson bad))) "invalid log sites accepted"
  rejected (EventLog.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (EventLog.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "name" (toJson "SynthesizedKeyedStorage"))) 10000)
    "keyed wrapper metadata accepted for the log profile"
  rejected (EventLog.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-keyed-storage-case.v1")) 10000)
    "keyed case schema accepted by the log tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2)) [⟨1, 2, 1⟩, ⟨2, 0, 2⟩]
  let value ← scenario plan [(2 ^ 255 + 7, 2 ^ 256 - 1), (6, 7), (14, 2 ^ 255)]
  let saved ← imported value
  let candidates ← get (EventLog.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (EventLog.shrinkCases saved 1000 10000)))
    "log reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut clearedFlags := false
  let mut removedSite := false
  let mut simplifiedSite := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (EventLog.caseProgram row)
    ensure (decide (EventLog.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "log reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", EventLog.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate log reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredInput := loweredInput || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.input.val < right.input.val)
    clearedFlags := clearedFlags || (sameCount && (reduced.transactions.zip value.transactions).any
      fun (left, right) => left.flags.val < right.flags.val && left.flags.bitAnd right.flags == left.flags)
    removedSite := removedSite || reduced.plan.sites.length < value.plan.sites.length
    simplifiedSite := simplifiedSite || (reduced.plan.sites.length == value.plan.sites.length &&
      reduced.plan.sites != value.plan.sites)
    changedStep := changedStep || Wire.encodeProgram reduced.plan.step.program != Wire.encodeProgram value.plan.step.program
    ensure (reduced.plan.sites.all fun site => value.plan.sites.any (·.guard == site.guard))
      "a log reduction moved a site to another guard"
    ensure ((← get (EventLog.replayCase row 10000)) == row) "reduced log case did not replay"
  ensure (removed && loweredInput && clearedFlags && removedSite && simplifiedSite && changedStep)
    "log shrink omitted sequence/input/flags/site/step axes"
  ensure ((← rows (← get (EventLog.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (EventLog.shrinkCases saved 0 10000)) "cases").isEmpty) "log shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (EventLog.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", EventLog.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", EventLog.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (EventLog.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict log reduction provenance accepted"

def testSourceEventLogCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceEventLogCases
end

section
-- leanmerge: from Solcore.Test.SourceEventLogCorpus
/-! The fixed event-log corpus checks actual original Core histories against
independently computed expectations: status, payload, slots zero and one, and
every committed log's emitter, topics and data after every transaction.
Coverage describes the checked step AST, the inputs and completions, and the
committed log counts, topic arities, data lengths and the guarded sites that
reverted transactions discard. Source/Rust/EVM agreement is a separate
external validation. -/
set_option autoImplicit false

namespace Tests.SourceEventLogCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", EventLog.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.EventLog.version),
  ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion),
  ("templateVersion", EventLog.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", EventLog.emitterVersion), ("wrapperVersion", EventLog.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := EventLog.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← EventLog.checkedPlan (← entry.getObjVal? "logPlan")
  let scenario ← EventLog.checkedScenario plan (← EventLog.decodeTransactions (← entry.getObjVal? "transactions"))
  EventLog.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "log-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

private def naturals (manifest : Json) (key : String) : Except String (List Nat) :=
  manifest.getObjValAs? (List Nat) key

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-logs" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected log manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("log manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words EventLog.boundaryInputs))
    "log corpus must require all six boundary inputs"
  require ((← naturals manifest "requiredHelperCounts") == [1, 2, 3] &&
    (← naturals manifest "requiredTransactionCounts") == [1, 2, 3])
    "log corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "log corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"]) "log corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "log corpus must require completion patterns"
  require ((← naturals manifest "requiredLogCounts") == [0, 1, 2, 3] &&
    (← naturals manifest "requiredTopicArities") == [0, 1, 2, 3, 4] &&
    (← naturals manifest "requiredDataSizes") == [0, 32, 64] &&
    (← naturals manifest "requiredDiscardedLogCounts") == [0, 1, 2, 3])
    "log corpus must require every log count, topic arity, data length and discarded count"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "log corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut logCounts : List Nat := []
  let mut arities : List Nat := []
  let mut sizes : List Nat := []
  let mut discarded : List Nat := []
  let mut transactionTotal := 0
  let mut logTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate log corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← EventLog.replayCase saved fuel) == saved) ("log corpus entry did not replay: " ++ identifier)
    let scenario ← EventLog.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "logPlan") == (← entry.getObjVal? "logPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported log entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("log corpus features changed: " ++ identifier)
    let history := EventLog.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    let statuses ← EventLog.checkShapes scenario history
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("log expected history length changed: " ++ identifier)
    for ((row, golden), tx) in (observed.zip expected).zip scenario.transactions do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage"),
        ("logs", ← row.getObjVal? "logs")]
      require (actual == golden) ("original Core differs from the independent history: " ++ identifier ++ " " ++ actual.compress)
      let logs ← row.getObjValAs? (List Json) "logs"
      logCounts := (logCounts ++ [logs.length]).eraseDups
      logTotal := logTotal + logs.length
      for log in logs do
        arities := (arities ++ [(← log.getObjValAs? (List String) "topics").length]).eraseDups
        sizes := (sizes ++ [((← string log "data").length - 2) / 2]).eraseDups
      if (← string row "status") == "reverted" then
        discarded := (discarded ++ [(EventLog.guardedSites scenario.plan tx).length]).eraseDups
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.map fun tx => toString tx.input.val).eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "log corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "log corpus misses an input"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "log corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "log corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "log corpus misses an observed outcome or completion pattern"
  require ([0, 1, 2, 3].all logCounts.contains && [0, 1, 2, 3, 4].all arities.contains &&
    [0, 32, 64].all sizes.contains && [0, 1, 2, 3].all discarded.contains)
    "log corpus misses a log count, topic arity, data length or discarded count"
  return Json.mkObj [("profile", toJson "stateful-logs"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("logs", toJson logTotal), ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid log corpus unexpectedly passed: " ++ message))

def testSourceEventLogCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-log-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first log case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated log case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let withRow := fun (row : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 row)))
  let row := history[0]!
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f'))))))
    "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7")))))))
    "changed slot"
  let logs ← checked (row.getObjValAs? (Array Json) "logs")
  let some log := logs[0]? | throw (IO.userError "first log history has no committed log")
  let topics ← checked (log.getObjValAs? (Array String) "topics")
  for (changed, reason) in [
      (logs.set! 0 (log.setObjVal! "topics" (toJson (topics.set! 0 "1"))), "changed topic"),
      (logs.set! 0 (log.setObjVal! "topics" (toJson topics.reverse)), "reordered topics"),
      (logs.set! 0 (log.setObjVal! "data" (toJson "0x")), "removed data"),
      (logs.set! 0 (log.setObjVal! "address" (toJson "3")), "changed emitter"),
      (logs.pop, "removed log"), (logs.push log, "duplicated log"), (logs.reverse, "reordered logs")] do
    rejects (validateManifest (withRow (row.setObjVal! "logs" (.arr changed)))) reason
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop)))) "popped history"
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let generatedStatus ← checked (generatedHistory[0]!.getObjValAs? String "status")
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status"
      (toJson (if generatedStatus == "returned" then "reverted" else "returned")))))))) "flipped status"
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "flags" (toJson "4"))))))) "changed flags"
  let plan ← checked (first.getObjVal? "logPlan")
  rejects (validateManifest (replace first (first.setObjVal! "logPlan" (plan.setObjVal! "sites" (toJson ([] : List Json))))))
    "removed sites"
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String))))) "features"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "generation"
    (Json.mkObj [("seed", toJson "13"), ("maxProgramNodes", toJson (384 : Nat))])))) "changed seed"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first)))) "duplicate entry"
  for (key, value) in [
      ("profile", toJson "stateful-keyed-storage"), ("framingVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredTopicArities", toJson [0, 1, 2, 3]), ("requiredDataSizes", toJson [0, 32]),
      ("requiredLogCounts", toJson [1, 2, 3]), ("requiredDiscardedLogCounts", toJson [1, 2, 3]),
      ("requiredCompletionPatterns", toJson (["reverted,reverted,reverted"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value)) key
  rejects (validateManifest manifest 0) "zero fuel"
  IO.println summary.compress

end Tests.SourceEventLogCorpus
end

section
-- leanmerge: from Solcore.Test.SourceEventLogEmitter
/-! Event-log protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover guarded sites, every frame
part, wrapping arithmetic, empty data, rollback of tentative logs and writes,
and the decoder's rejection of malformed journals. -/
set_option autoImplicit false

namespace Tests.SourceEventLogEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (sites : List Site) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "log step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step sites |
    throw (IO.userError "log wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.EventLog.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"log source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat)) : List EventLogExecution.Transaction :=
  rows.zipIdx.map fun ((flags, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def logRow (topics data : List Nat) : Json := Json.mkObj [
  ("address", toJson "2"), ("topics", toJson (topics.map toString)),
  ("data", toJson ("0x" ++ String.join (data.map hexWord)))]

private def slotRows (slot0 slot1 : Nat) : Json := toJson [
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]]

/-- One hand-computed row: status, payload, slots zero and one, and logs. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat) × List Json)) : IO Unit := do
  let history := EventLogExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "log golden history did not complete"
  for (row, (status, payload, (slot0, slot1), logs)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some ("0x" ++ hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slot0 slot1) &&
      (row.getObjVal? "logs").toOption == some (toJson logs))
      s!"log golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: the result is input + slot 0 and each site value is result + guard.
  let identity ← checked [.var 0] [⟨1, 2, 1⟩, ⟨3, 0, 2⟩]
  historyCheck identity [(2, 5), (9, 1), (8, 0)] [
    ("returned", 5, (5, 1), [logRow [7, 8] [6]]),
    ("reverted", 6, (5, 1), []),
    ("returned", 5, (5, 2), [logRow [] [8, 5]])]
  -- step(x) = x + 1 wraps at the maximum; LOG4 without data; a revert keeps
  -- the committed slots and commits none of its guarded logs.
  let incremented ← checked [increment] [⟨2, 4, 0⟩]
  historyCheck incremented [(4, maximum), (5, 3), (2 ^ 255 + 6, 2)] [
    ("returned", 0, (0, 1), [logRow [4, 5, 6, 7] []]),
    ("reverted", 4, (0, 1), []),
    ("returned", 3, (3, 2), [logRow [7, 8, 9, 10] []])]
  -- No site: flags select only the completion.
  historyCheck (← checked [.var 0] []) [(14, 7), (15, 1)] [
    ("returned", 7, (7, 1), []), ("reverted", 8, (7, 1), [])]

/-- The reverted call's working journal holds every frame record in order; the
public runtime commits the empty checkpoint journal and the prior world. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0] [⟨1, 1, 1⟩, ⟨2, 0, 0⟩]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "log contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero,
    inputData := EventLogExecution.inputData (Word.ofNatModulo 7) (Word.ofNatModulo 3) }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed a log call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "log golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 3)))
        "odd flags did not revert with the result"
      let records := result.workingJournal.logList.map fun entry => (entry.emitter.val, entry.topic.val, entry.payload.val)
      ensure (records == [(2, 256 + 16 + 1, 0), (2, 513, 4), (2, 769, 5), (2, 256, 0)])
        s!"working journal lost the frame order: {reprStr records}"
      ensure (result.committedJournal.logList.isEmpty) "reverted logs were committed"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ((committed.storageValue? Word.zero).isNone && (committed.storageValue? (Word.ofNatModulo 1)).isNone)
        "reverted writes were committed"

private def record (topic payload : Nat) (emitter : Nat := 2) : CheckedCoreWordLog :=
  ⟨⟨emitter % addressModulus, Nat.mod_lt _ (by decide)⟩, Word.ofNatModulo topic, Word.ofNatModulo payload⟩

private def decodes (records : List CheckedCoreWordLog) : Option (List (List Nat × List Nat)) :=
  match EventLogExecution.decodeJournal records with
  | .ok events => some (events.map fun event => (event.topics.map (·.val), event.data.map (·.val)))
  | .error _ => none

private def framingChecks : IO Unit := do
  ensure (decodes [] == some []) "empty journal did not decode to no logs"
  ensure (decodes [record 256 0] == some [([], [])]) "LOG0 without data did not decode"
  ensure (decodes [record (256 + 32 + 4) 0, record 513 9, record 514 8, record 769 1, record 770 2,
      record 771 3, record 772 4, record (256 + 1) 0, record 769 5] ==
      some [([1, 2, 3, 4], [9, 8]), ([5], [])]) "complete frames did not decode in order"
  for (records, reason) in [
      ([record 255 0], "a record below the header range"),
      ([record 256 1], "a nonzero header payload"),
      ([record (256 + 5) 0, record 769 1, record 770 1, record 771 1, record 772 1, record 773 1], "five topics"),
      ([record (256 + 48) 0, record 513 1, record 514 1, record 515 1], "three data Words"),
      ([record (256 + 2) 0, record 769 1], "a truncated frame"),
      ([record (256 + 2) 0, record 770 1, record 769 1], "topics out of order"),
      ([record (256 + 16) 0, record 769 1], "a topic in place of data"),
      ([record (256 + 1) 0, record 769 1 3], "mixed emitters"),
      ([record 256 0, record 513 1], "a record after the frames")] do
    ensure (decodes records).isNone s!"decoder accepted {reason}"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment] [⟨1, 4, 2⟩, ⟨2, 0, 0⟩, ⟨3, 3, 1⟩], ← checked [.var 0] []] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "log plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (Wire.programNodes plan.program == Wire.programNodes plan.step.program + EventLog.programOverhead plan.sites)
      "log wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "log wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "log wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "log emission is nondeterministic"
  let some step := Aggregates.CheckedDAG.ofParts? [.var 0] entry | throw (IO.userError "identity step rejected")
  for sites in [[⟨0, 1, 1⟩], [⟨4, 1, 1⟩], [⟨1, 5, 0⟩], [⟨1, 0, 3⟩], [⟨2, 0, 0⟩, ⟨1, 0, 0⟩],
      [⟨2, 0, 0⟩, ⟨2, 1, 0⟩], [⟨1, 0, 0⟩, ⟨2, 0, 0⟩, ⟨3, 0, 0⟩, ⟨3, 1, 0⟩]] do
    ensure (CheckedPlan.ofParts? step sites).isNone s!"invalid log sites admitted: {reprStr sites}"
  ensure (EventLog.programOverhead [⟨1, 4, 2⟩] > EventLog.programOverhead [⟨1, 3, 2⟩] &&
    EventLog.programOverhead [⟨1, 3, 2⟩] > EventLog.programOverhead [⟨1, 3, 1⟩] &&
    EventLog.programOverhead [⟨1, 3, 1⟩] > EventLog.programOverhead [])
    "log-site simplification does not shrink the program"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mload, mstore, revert_, log0 as sc_log0, log2 as sc_log2} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedLogs {",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = sload(0);", "        let sc_count: word = sload(1);",
  "        let sc_result: word = sc_step(sc_input + sc_old);",
  "        sstore(0, sc_result);", "        sstore(1, sc_count + 1);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
  "        if ((sc_flags & 2) == 2) {",
  "            let sc_value1: word = sc_step(sc_result + 1);",
  "            sc_log0(sc_ptr, 0);", "        }",
  "        if ((sc_flags & 8) == 8) {",
  "            let sc_value3: word = sc_step(sc_result + 3);",
  "            mstore(sc_ptr, sc_value3);", "            mstore(sc_ptr + 32, sc_result);",
  "            sc_log2(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2);", "        }",
  "        if ((sc_flags & 1) == 1) {", "            mstore(sc_ptr, sc_result);",
  "            revert_(sc_ptr, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment] [⟨1, 0, 0⟩, ⟨3, 2, 2⟩])
  ensure (source.source == expectedBasic) "log protocol source changed"
  ensure (source.contractName == "SynthesizedLogs" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedLogsDeploy"] && source.runtimePath == ["SynthesizedLogsDeploy", "SynthesizedLogs"])
    "log wrapper metadata changed"
  let none ← emitted (← checked [increment] [])
  ensure ((none.source.splitOn "import {sload, sstore, mload, mstore, revert_} from std.opcodes;").length == 2 &&
    (none.source.splitOn "sc_log").length == 1) "a plan without sites imported or called a log wrapper"
  let one ← emitted (← checked [increment] [⟨2, 4, 1⟩])
  ensure ((one.source.splitOn "revert_, log4 as sc_log4} from std.opcodes;").length == 2 &&
    (one.source.splitOn "            sc_log4(sc_ptr, 32, sc_value2 + 1, sc_value2 + 2, sc_value2 + 3, sc_value2 + 4);").length == 2)
    "LOG4 import or call changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)] [⟨1, 1, 0⟩])
  ensure ((divided.source.splitOn "import {sload, sstore, mload, mstore, revert_, log1 as sc_log1, div as sc_div, ").length == 2)
    "log emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.EventLog.emitterVersion == "solcore-source-event-log-v1" &&
    Solcore.Synthesis.Source.EventLog.wrapperVersion == "solcore-word-event-log-contract-v1" &&
    Solcore.Synthesis.Source.EventLog.selector == "0x7357f5d2" &&
    EventLog.version == "core-event-log-contract-v1" && EventLog.framingVersion == "core-word-log-framing-v1")
    "log provenance changed"

private def observerChecks : IO Unit := do
  ensure (EventLogExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "log calldata is not selector, flags and input Words"
  let plan ← checked [.var 0] [⟨1, 1, 1⟩]
  let calls := transactions [(2, 2), (3, 1), (0, 0)]
  let exhausted := EventLogExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    rows.length == 1 && (rows[0]!.getObjVal? "logs").toOption == some Json.null &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "log observer conflated fuel exhaustion with completion or claimed unknown logs"
  let complete := EventLogExecution.observe plan calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1"] : List String)) &&
    (complete.getObjVal? "initialLogs").toOption == some (toJson ([] : List Json)) &&
    (complete.getObjValAs? String "framing").toOption == some "core-word-log-framing-v1")
    "history did not declare its slots, deployment logs or framing"

def testSourceEventLogEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  framingChecks
  formattingChecks
  observerChecks

end Tests.SourceEventLogEmitter
end

section
-- leanmerge: from Solcore.Test.SourceRevertDataCases
/-! The `runtime-revert-data` profile. Its Core reference returns the
accumulator or the revert data of the first site whose condition decides; it
agrees with a direct interpreter that runs each helper and closure as a
function over byte lists and stops at a site with its data, on generated
plans, and two fixtures' sources and results are golden, the results from a
separate Python model. Admission refuses helpers, sites, payloads, steps and
counts outside the profile; generation draws every shape and replays
exactly; tampering is refused, and reductions are strictly smaller and
replay. -/
set_option autoImplicit false

namespace Tests.SourceRevertDataCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.RevertData
open Solcore.Synthesis.Core.MemoryValues (Operand Fold Action Part)
open Solcore.Synthesis.Source

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private def fuel : Nat := 1000000

private def modulus : Nat := 2 ^ 256

private def cases (corpus : Json) : IO (Array Json) :=
  expect (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := expect (case.getObjVal? "provenance")

private def wordBytes (value : Nat) : List Nat := (List.range 32).map fun index => (value / 256 ^ (31 - index)) % 256

private def bigEndian (bytes : List Nat) : Nat := bytes.foldl (fun total byte => total * 256 + byte) 0

private def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

/-- A run's result: a returned Word, revert data, or a `runtime-halts` halt. -/
private inductive Result where
  | returned (word : Nat)
  | reverted (data : List Nat)
  | halted
  deriving BEq, Repr

/-- A returned Word in decimal, revert data in hex, a halt as `invalid`. -/
private def Result.text : Result → String
  | .returned word => toString word
  | .reverted data => "0x" ++ String.ofList (data.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])
  | .halted => "invalid"

private def run (program : Solcore.Core.Wire.Program) : IO Result :=
  match program.toCore.runStateful fuel with
  | .done (.inLeft _ (.word value)) _ => pure (.returned value.val)
  | .done (.inRight _ (.pair (.word length) (.pair (.word first) (.word second)))) _ =>
      if length.val ≤ 64 then pure (.reverted ((wordBytes first.val ++ wordBytes second.val).take length.val))
      else if length.val = haltLength && first.val = 0 && second.val = 0 then pure .halted
      else throw (IO.userError "a reference program reverted with more than 64 bytes")
  | _ => throw (IO.userError "a reference program returned neither a Word nor revert data")

/-! A direct interpreter of a plan: bytes values as byte lists in a store of
objects, variables naming an object, `Error` values as a selector Word,
empty, or the object a message names, so that a message's data are its
object's bytes when a site raises it, and each helper and closure run as a
function of its `Error` and Word. A site stops the run with its data. It
shares no code with the Core reference. -/

private inductive Err where
  | selector (word : Nat)
  | empty
  | message (object : Nat)
  deriving Inhabited, BEq

private structure Machine where
  input : Nat
  objects : Array (Array Nat) := #[]
  bytes : Array (Option Nat) := #[]
  errors : Array Err := #[]
  pairs : Array (Option Err × Option Nat) := #[]
  sums : Array (Option Err × Option Nat) := #[]
  enums : Array (Option Err × Option Nat) := #[]
  closures : Array (Site × Fold × Nat) := #[]
  acc : Nat := 0
  counter : Option Nat := none

private inductive Stop where
  | revert (data : List Nat)
  | halt
  | fault (message : String)

private abbrev Interp := StateT Machine (Except Stop)

private def fault {α : Type} (message : String) : Interp α := throw (.fault message)

/-- A Word of `run`, or of a helper or closure whose parameter is `base`. -/
private def operand (base : Option Nat) (value : Operand) : Interp Nat := do
  let machine ← getThe Machine
  let own := base.getD machine.input
  match value with
  | .input => return own
  | .add constant => return (own + constant) % modulus
  | .mul constant => return (own * constant) % modulus
  | .xor constant => return own ^^^ constant
  | .acc => return machine.acc
  | .counter => match machine.counter with
    | some counter => return counter
    | none => fault "a counter outside a loop"

private def objectOf (value : Nat) : Interp Nat := do
  match (← getThe Machine).bytes[value]? with
  | some (some object) => return object
  | _ => fault "a bytes value out of scope"

private def contents (object : Nat) : Interp (List Nat) := do
  return (((← getThe Machine).objects[object]?).getD #[]).toList

private def dataOf : Err → Interp (List Nat)
  | .selector word => return (wordBytes word).drop 28
  | .empty => return []
  | .message object => contents object

private def made (base : Option Nat) : Make → Interp Err
  | .selector word => do return .selector (← operand base word)
  | .empty => return .empty
  | .message value => do return .message (← objectOf value)

private def origin (base : Option Nat) (param : Option Err) : Source → Interp Err
  | .make making => made base making
  | .named number => do
      match (← getThe Machine).errors[number]? with
      | some error => return error
      | none => fault "an Error variable out of scope"
  | .param => match param with
      | some error => return error
      | none => fault "no Error parameter"

private def holds (word : Nat) : Test → Bool
  | .lt constant => word < constant
  | .gt constant => word > constant
  | .eq constant => word == constant
  | .ne constant => word != constant
  | .bits mask value => word &&& mask == value

private def literalBytes (text : Nat) : List Nat := (literals.getD text "").toUTF8.toList.map (·.toNat)

/-- An `if` site raises when its condition holds, a `require` or `assert`
when it fails; a halt site stops without data. -/
private def raiseAt (base : Option Nat) (param : Option Err) (single : Site) : Interp Unit := do
  let condition := holds (← operand base single.cond.word) single.cond.test
  if condition == (single.form == .when) then
    let data ← match single.payload with
      | .error source => do dataOf (← origin base param source)
      | .literal text => pure (literalBytes text)
      | .none => pure []
      | .halt _ => throw .halt
    throw (.revert data)

private def combine (fold : Fold) (left right : Nat) : Nat :=
  match fold with
  | .add => (left + right) % modulus
  | .xor => left ^^^ right

private def accumulate (fold : Fold) (constant observed : Nat) : Interp Unit := modify fun machine =>
  {machine with acc := combine fold ((machine.acc * constant) % modulus) observed}

private def partBytes : Part → Interp (List Nat)
  | .word value => do return wordBytes (← operand none value)
  | .zeros count => return List.replicate count 0
  | .value (.bytes value) => do contents (← objectOf value)
  | .value _ => fault "a part outside the profile"

/-- The profile's actions; `slot` is a loop body's own variable. -/
private def act (slot : Option Nat) : Action → Interp Unit
  | .bytes build => do
      let parts := match build with
        | .toBytes single => [single]
        | .concat left right => [left, right]
      let mut data : List Nat := []
      for single in parts do
        data := data ++ (← partBytes single)
      let object := (← getThe Machine).objects.size
      modify fun machine => {machine with objects := machine.objects.push data.toArray}
      match slot with
      | some index => modify fun machine => {machine with bytes := machine.bytes.set! index (some object)}
      | none => modify fun machine => {machine with bytes := machine.bytes.push (some object)}
  | .alias (.bytes value) => do
      let object ← objectOf value
      modify fun machine => {machine with bytes := machine.bytes.push (some object)}
  | .write (.bytes value) (.literal position) written width _ => do
      let object ← objectOf value
      let word ← operand none written
      modify fun machine => {machine with objects := machine.objects.modify object fun bytes =>
        match width with
        | .word => (wordBytes word).zipIdx.foldl (fun bytes (byte, k) => bytes.set! (position + k) byte) bytes
        | .byte => bytes.set! position (word % 256)}
  | .observe fold constant (.bytes value) access => do
      let data ← contents (← objectOf value)
      let observed ← match access with
        | .length => pure data.length
        | .word (.literal position) => pure (bigEndian ((data.drop position).take 32))
        | .byte (.literal position) => pure (data.getD position 0)
        | _ => fault "an access outside the profile"
      accumulate fold constant observed
  | _ => fault "an action outside the profile"

/-- A `raise` or `call` helper on its `Error` and Word: its result. -/
private def raiseCall (helpers : List Helper) : Nat → Nat → Err → Nat → Interp Nat
  | 0, _, _, _ => fault "a chain of calls too deep"
  | fuel + 1, number, error, word => do
      match helpers[number]? with
      | some (.call callee constant) => raiseCall helpers fuel callee error ((word + constant) % modulus)
      | some (.raise single fold constant) => do
          raiseAt (some word) (some error) single
          return combine fold word constant
      | _ => fault "a call of a helper that does not raise"

private def declared (helpers : List Helper) : Decl → Interp Err
  | .make making => made none making
  | .helper helper word => do
      match helpers[helper]? with
      | some (.make constant) => return .selector (((← operand none word) + constant) % modulus)
      | _ => fault "a made Error without a make helper"
  | .message _ value => do return .message (← objectOf value)
  | .pick helper word first second => do
      match helpers[helper]? with
      | some (.pick test) =>
          let chosen ← origin none none first
          let other ← origin none none second
          return if holds (← operand none word) test then chosen else other
      | _ => fault "a picked Error without a pick helper"

private def held (error : Option Source) (word : Option Operand) : Interp (Option Err × Option Nat) := do
  let error ← match error with
    | some source => some <$> origin none none source
    | none => pure none
  let word ← match word with
    | some value => some <$> operand none value
    | none => pure none
  return (error, word)

private def runStep (helpers : List Helper) : Step → Interp Unit
  | .action single => act none single
  | .error decl => do
      let error ← declared helpers decl
      modify fun machine => {machine with errors := machine.errors.push error}
  | .data datum => do
      match datum with
      | .pair error word => do
          let value ← held (some error) (some word)
          modify fun machine => {machine with pairs := machine.pairs.push value}
      | .inl error => do
          let value ← held (some error) none
          modify fun machine => {machine with sums := machine.sums.push value}
      | .inr word => do
          let value ← held none (some word)
          modify fun machine => {machine with sums := machine.sums.push value}
      | .first error word => do
          let value ← held (some error) (some word)
          modify fun machine => {machine with enums := machine.enums.push value}
      | .second word => do
          let value ← held none (some word)
          modify fun machine => {machine with enums := machine.enums.push value}
  | .site single => raiseAt none none single
  | .call helper error word _ fold constant => do
      let error ← origin none none error
      let result ← raiseCall helpers (maximumHelpers + 1) helper error (← operand none word)
      accumulate fold constant result
  | .take target single fold constant => do
      let machine ← getThe Machine
      let entry := match target with
        | .pair number => machine.pairs[number]?
        | .sum number => machine.sums[number]?
        | .enum number => machine.enums[number]?
      let some (error, word) := entry | fault "a data value out of scope"
      if let some error := error then raiseAt none (some error) single
      if let some word := word then accumulate fold constant word
  | .closure single fold constant => modify fun machine =>
      {machine with closures := machine.closures.push (single, fold, constant)}
  | .apply number word fold constant => do
      let some (single, own, added) := (← getThe Machine).closures[number]? | fault "a missing closure"
      let argument ← operand none word
      raiseAt (some argument) none single
      accumulate fold constant (combine own argument added)
  | .loop mask body => do
      let outer := (← getThe Machine).bytes.size
      let own := (body.filter fun item => item matches .action _).length
      modify fun machine => {machine with bytes := machine.bytes ++ (List.replicate own none).toArray}
      for counter in List.range ((← getThe Machine).input &&& mask) do
        modify fun machine => {machine with counter := some counter}
        let mut slot := outer
        for item in body do
          match item with
          | .action single =>
              act (some slot) single
              slot := slot + 1
          | .site single => raiseAt none none single
      modify fun machine =>
        {machine with counter := none, bytes := machine.bytes.extract 0 outer ++ (List.replicate own none).toArray}

/-- The returned Word or the revert data; `none` for a plan it cannot run. -/
private def interpret (plan : Plan) (input : Nat) : Option Result :=
  match (plan.steps.forM (runStep plan.helpers)).run {input} with
  | .ok ((), machine) => some (.returned machine.acc)
  | .error (.revert data) => some (.reverted data)
  | .error .halt => some .halted
  | .error (.fault _) => none

private def boundary : List Nat := [0, 1, 2, 255, 256, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 - 1]

/-- The reference agrees with the interpreter on 200 generated plans at the
eight boundary inputs and four others. -/
private def modelChecks : IO Unit := do
  let mut compared := 0
  let mut reverted := 0
  let mut lengths : List Nat := []
  for seed in List.range 200 do
    match RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
          if let .reverted data := core then
            reverted := reverted + 1
            unless lengths.contains data.length do lengths := data.length :: lengths
  ensure (compared = 2400) "fewer than 200 generated plans compared with the interpreter"
  ensure (reverted ≥ 600 && compared - reverted ≥ 600) "fewer than 600 compared outcomes reverted or returned"
  for length in [0, 1, 4, 31, 32, 33, 63, 64] do
    ensure (lengths.contains length) s!"no compared outcome reverted with {length} bytes"

/-! Two fixtures. The first makes a selector through a helper and a message of
a 64-byte value, reverts with a literal, writes a byte of the message's value,
passes the message through a function value to a helper calling a `require`
helper, takes a sum holding the selector, applies a closure with a 63-byte
`require` literal, raises a message of a value a bounded loop allocates, and
reads the written value. The second makes a message of a 5-byte value through
a helper, picks it or `Error.Empty` by the input, writes through a second
variable of the value, takes a pair holding the picked `Error`, calls a helper
raising its own selector, takes an enum holding the message, then reverts
empty on the accumulator and with a 64-byte `require` literal. -/

private def fixtureA : Plan := {
  helpers := [
    .raise {form := .require, cond := {word := .input, test := .lt 1000}, payload := .error .param} .add 3,
    .make 7,
    .call 0 9],
  steps := [
    .action (.bytes (.concat (.word .input) (.word (.mul 3)))),
    .error (.helper 1 (.xor 9)),
    .error (.make (.message 0)),
    .site {form := .when, cond := {word := .input, test := .bits 3 2}, payload := .literal 3},
    .action (.write (.bytes 0) (.literal 31) (.add 1) .byte .inline),
    .call 2 (.named 1) (.add 5) false .xor 5,
    .data (.inl (.named 0)),
    .take (.sum 0) {form := .when, cond := {word := .input, test := .gt 255}, payload := .error .param} .add 7,
    .closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .literal 8} .add 3,
    .apply 0 .input .xor 9,
    .loop 3 [.action (.bytes (.toBytes (.word .counter))),
      .site {form := .when, cond := {word := .counter, test := .eq 2}, payload := .error (.make (.message 1))}],
    .action (.observe .add 3 (.bytes 0) (.word (.literal 0)))]}

private def fixtureB : Plan := {
  helpers := [
    .message,
    .pick (.bits 1 1),
    .raise {form := .when, cond := {word := .xor 255, test := .eq 0}, payload := .error (.make (.selector (.add 2)))}
      .xor 7],
  steps := [
    .action (.bytes (.toBytes (.zeros 5))),
    .action (.alias (.bytes 0)),
    .error (.message 0 0),
    .error (.pick 1 .input (.named 0) (.make .empty)),
    .action (.write (.bytes 1) (.literal 4) .input .byte .helper),
    .data (.pair (.named 1) (.add 1)),
    .take (.pair 0) {form := .require, cond := {word := .input, test := .ne 256}, payload := .error .param} .add 5,
    .call 2 (.make .empty) .input true .add 3,
    .data (.first (.named 0) (.mul 3)),
    .take (.enum 0) {form := .when, cond := {word := .input, test := .eq 2}, payload := .error .param} .xor 11,
    .site {form := .when, cond := {word := .acc, test := .bits 7 5}, payload := .none},
    .site {form := .require, cond := {word := .input, test := .lt (2 ^ 255)}, payload := .literal 9}]}

/-- From the Python model of `Tests/scripts/test-semantic-revert-data-corpus.py`:
a returned Word in decimal, revert data in hex. -/
private def fixtureAResults : List (Nat × String) := [
  (0, "463"),
  (1, "0x74686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f672030313233343536373839206162636465666768"),
  (2, "0x746f6f206c61726765"),
  (255, "0x0000000000000000000000000000000000000000000000000000000000000002"),
  (256, "0x00000110"),
  (2 ^ 256 - 1, "0xfffffffd"),
  (2 ^ 255, "0x80000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000000"),
  (2 ^ 255 - 1, "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd"),
  (3, "0x0000000000000000000000000000000000000000000000000000000000000002"),
  (5, "624"),
  (6, "0x746f6f206c61726765"),
  (1001, "0x00000000000000000000000000000000000000000000000000000000000003ea0000000000000000000000000000000000000000000000000000000000000bbb")]

private def fixtureBResults : List (Nat × String) := [
  (0, "110"),
  (1, "135"),
  (2, "0x0000000002"),
  (255, "0x00000101"),
  (256, "0x"),
  (2 ^ 256 - 1, "0x"),
  (2 ^ 255, "0x74686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67203031323334353637383920616263646566676869"),
  (2 ^ 255 - 1, "0x"),
  (3, "185"),
  (5, "211"),
  (6, "224"),
  (1001, "42975")]

private def header : List String := [
  "import * from std;",
  "import * from std.dispatch;",
  "import { mload, mstore, mstore8, shr, mod } from std.opcodes;",
  ""]

private def fixtureASource : String := String.intercalate "\n" (header ++ [
  "function sc_word<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
  "    return mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 32)));",
  "}",
  "",
  "function sc_h0(sc_e: Error, sc_w: word) returns (word) {",
  "    require((sc_w < 1000), sc_e);",
  "    return (sc_w + 3);",
  "}",
  "",
  "function sc_h1(sc_w: word) returns (Error) {",
  "    return Error((sc_w + 7));",
  "}",
  "",
  "function sc_h2(sc_e: Error, sc_w: word) returns (word) {",
  "    return sc_h0(sc_e, (sc_w + 9));",
  "}",
  "",
  "contract SynthesizedRevertData {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = concat(bytes32(sc_x), bytes32((sc_x * 3)));",
  "        let sc_e0: Error = sc_h1((sc_x ^ 9));",
  "        let sc_e1: Error = Error.Msg(memory(Typedef.rep(sc_b0)));",
  "        if ((sc_x & 3) == 2) {",
  "            revertLit(\"too large\");",
  "        }",
  "        mstore8(MemoryPointer.ptr(truncate(slice_(sc_b0, 31), 1)), (sc_x + 1));",
  "        let sc_f0: function (Error, word) returns (word) = sc_h2;",
  "        sc_r = ((sc_r * 5) ^ sc_f0(sc_e1, (sc_x + 5)));",
  "        let sc_u0: sum<Error, word> = inl(sc_e0);",
  "        match (sc_u0) {",
  "            case inl(sc_e) {",
  "                if (sc_x > 255) {",
  "                    revertWithError(sc_e);",
  "                }",
  "            }",
  "            case inr(sc_w) {",
  "                sc_r = ((sc_r * 7) + sc_w);",
  "            }",
  "        }",
  "        let sc_c0: function (word) returns (word) = lam (sc_j: word) -> word {",
  "            require((sc_j != 1), \"the quick brown fox jumps over the lazy dog 0123456789 abcdefgh\");",
  "            return (sc_j + 3);",
  "        };",
  "        sc_r = ((sc_r * 9) ^ sc_c0(sc_x));",
  "        let sc_limit: word = (sc_x & 3);",
  "        let sc_counter: word = 0;",
  "        while (sc_limit > sc_counter) {",
  "            let sc_b1: memory<bytes> = to_bytes(bytes32(sc_counter));",
  "            if (sc_counter == 2) {",
  "                revertWithError(Error.Msg(memory(Typedef.rep(sc_b1))));",
  "            }",
  "            sc_counter = (sc_counter + 1);",
  "        }",
  "        sc_r = ((sc_r * 3) + sc_word(sc_b0, 0));",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureBSource : String := String.intercalate "\n" (header ++ [
  "function sc_put8<a>(sc_v: a, sc_i: word, sc_w: word) returns (()) where a: MemorySize, a: MemoryPointer {",
  "    mstore8(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1)), sc_w);",
  "}",
  "",
  "enum Sc_F {",
  "    Sc_F0(Error, word),",
  "    Sc_F1(word)",
  "}",
  "",
  "function sc_h0(sc_v: memory<bytes>) returns (Error) {",
  "    return Error.Msg(memory(Typedef.rep(sc_v)));",
  "}",
  "",
  "function sc_h1(sc_w: word, sc_a: Error, sc_b: Error) returns (Error) {",
  "    if ((sc_w & 1) == 1) {",
  "        return sc_a;",
  "    }",
  "    return sc_b;",
  "}",
  "",
  "function sc_h2(sc_e: Error, sc_w: word) returns (word) {",
  "    if ((sc_w ^ 255) == 0) {",
  "        revertWithError(Error((sc_w + 2)));",
  "    }",
  "    return (sc_w ^ 7);",
  "}",
  "",
  "contract SynthesizedRevertData {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = to_bytes(empty(5));",
  "        let sc_b1: memory<bytes> = sc_b0;",
  "        let sc_e0: Error = sc_h0(sc_b0);",
  "        let sc_e1: Error = sc_h1(sc_x, sc_e0, Error.Empty);",
  "        sc_put8(sc_b1, 4, sc_x);",
  "        let sc_t0: (Error, word) = (sc_e1, (sc_x + 1));",
  "        match (sc_t0) {",
  "            case (sc_e, sc_w) {",
  "                require((sc_x != 256), sc_e);",
  "                sc_r = ((sc_r * 5) + sc_w);",
  "            }",
  "        }",
  "        sc_r = ((sc_r * 3) + sc_h2(Error.Empty, sc_x));",
  "        let sc_g0: Sc_F = Sc_F.Sc_F0(sc_e0, (sc_x * 3));",
  "        match (sc_g0) {",
  "            case Sc_F.Sc_F0(sc_e, sc_w) {",
  "                if (sc_x == 2) {",
  "                    revertWithError(sc_e);",
  "                }",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "            case Sc_F.Sc_F1(sc_w) {",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "        }",
  "        if ((sc_r & 7) == 5) {",
  "            revertEmpty();",
  "        }",
  "        require((sc_x < 57896044618658097711785492504343953926634992332820282019728792003956564819968), " ++
    "\"the quick brown fox jumps over the lazy dog 0123456789 abcdefghi\");",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def fixtureAShapes : List (String × List String) := [
  ("helpers", ["call", "make", "raise"]),
  ("forms", ["require", "requireLiteral", "revertLit", "revertWithError"]),
  ("errors", ["message", "selector"]),
  ("contexts", ["call", "closure", "loop", "run", "sum"]),
  ("carriers", ["held", "loop", "value"]),
  ("declarations", ["made", "variable"]),
  ("data", ["inl"]),
  ("tests", ["bits", "eq", "gt", "lt", "ne"]),
  ("words", ["counter", "input", "local"]),
  ("lengths", ["1-31", "32", "33-63", "64"]),
  ("hazards", ["written"]),
  ("steps", ["action", "apply", "call", "closure", "data", "error", "loop", "site", "take"])]

private def fixtureBShapes : List (String × List String) := [
  ("helpers", ["message", "pick", "raise"]),
  ("forms", ["require", "requireLiteral", "revertEmpty", "revertWithError"]),
  ("errors", ["message", "picked", "selector"]),
  ("contexts", ["enum", "helper", "pair", "run"]),
  ("carriers", ["held", "inline"]),
  ("declarations", ["messaged", "picked"]),
  ("data", ["enum0", "pair"]),
  ("tests", ["bits", "eq", "lt", "ne"]),
  ("words", ["acc", "input", "local"]),
  ("lengths", ["0", "1-31", "64"]),
  ("hazards", ["alias", "written"]),
  ("steps", ["action", "call", "data", "error", "site", "take"])]

private def fixtureChecks : IO Unit := do
  for (label, plan, source, results, shapes) in [
      ("first", fixtureA, fixtureASource, fixtureAResults, fixtureAShapes),
      ("second", fixtureB, fixtureBSource, fixtureBResults, fixtureBShapes)] do
    ensure plan.admitted s!"the {label} fixture plan is not admitted"
    let some checked := RevertData.CheckedPlan.ofPlan? plan
      | throw (IO.userError s!"the {label} fixture failed the checker")
    ensure ((RevertData.emit plan).source == source) s!"the {label} fixture source changed"
    for (value, expected) in results do
      ensure ((← run (checked.program (Word.ofNatModulo value))).text == expected) s!"{label} fixture input {value}: Core result"
      ensure ((interpret plan value).map Result.text == some expected) s!"{label} fixture input {value}: interpreter result"
    ensure (plan.shapes == shapes) s!"the {label} fixture shapes changed"
    ensure (match RevertData.planOf (RevertData.planJson plan) with
      | .ok decoded => decoded == plan
      | .error _ => false) s!"the {label} fixture plan JSON does not round-trip"
  let some first := RevertData.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  let some second := RevertData.CheckedPlan.ofPlan? fixtureB
    | throw (IO.userError "the second fixture failed the checker")
  ensure (RevertData.observe first (Word.ofNatModulo 256) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0x00000110")])
    "a selector's low four bytes are not observed as the revert data"
  ensure (RevertData.observe second (Word.ofNatModulo 256) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0x")])
    "an empty revert is not observed as empty revert data"

private def withStep (plan : Plan) (index : Nat) (replacement : Step) : Plan :=
  {plan with steps := plan.steps.set index replacement}

private def withHelper (plan : Plan) (index : Nat) (replacement : Helper) : Plan :=
  {plan with helpers := plan.helpers.set index replacement}

/-- Admission refuses what the compiler, the lowerings or the reference
cannot take. -/
private def admissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.admitted) s!"admitted {label}"
  let admitted := fun (label : String) (plan : Plan) => ensure plan.admitted s!"refused {label}"
  let a := fixtureA
  let b := fixtureB
  let bytes := Step.action (.bytes (.concat (.word .input) (.word .input)))
  let observe := Step.action (.observe .add 3 (.bytes 0) .length)
  let quiet : Site := {form := .when, cond := {word := .input, test := .eq 0}, payload := .none}
  let plain := fun (steps : List Step) => ({helpers := [], steps} : Plan)
  let raising := fun (steps : List Step) => ({helpers := [.raise quiet .add 3], steps} : Plan)
  let call := Step.call 0 (.make .empty) .input false .add 3
  let siteA := fun (payload : Payload) => withStep a 3 (.site {form := .when, cond := {word := .input, test := .bits 3 2}, payload})
  let testA := fun (test : Test) =>
    withStep a 7 (.take (.sum 0) {form := .when, cond := {word := .input, test}, payload := .error .param} .add 7)
  let helperB := fun (word : Operand) (payload : Payload) =>
    withHelper b 2 (.raise {form := .when, cond := {word, test := .eq 0}, payload} .xor 7)
  let loop := fun (mask : Nat) (body : List Item) => plain [bytes, .loop mask body, observe]
  admitted "a site and an observation" (plain [bytes, .site quiet, observe])
  refused "four helpers" ({a with helpers := a.helpers ++ [.message]} : Plan)
  refused "no step" ({a with steps := []} : Plan)
  refused "thirteen steps" ({a with steps := a.steps ++ [observe]} : Plan)
  refused "no site" (plain [bytes, observe])
  refused "no fold" (plain [.site quiet])
  refused "a helper calling itself" (withHelper a 2 (.call 2 9))
  refused "a helper calling a later one" (withHelper a 0 (.call 2 9))
  refused "a call of a make helper" (withHelper a 2 (.call 1 9))
  refused "a call constant of 0" (withHelper a 2 (.call 0 0))
  refused "a call constant of 256" (withHelper a 2 (.call 0 256))
  refused "a make constant of 0" (withHelper a 1 (.make 0))
  refused "a make constant of 256" (withHelper a 1 (.make 256))
  refused "an even fold constant" (withHelper a 0
    (.raise {form := .require, cond := {word := .input, test := .lt 1000}, payload := .error .param} .add 4))
  refused "the accumulator in a helper" (helperB .acc (.error (.make (.selector (.add 2)))))
  refused "a selector of the accumulator in a helper" (helperB (.xor 255) (.error (.make (.selector .acc))))
  refused "a message in a helper" (helperB (.xor 255) (.error (.make (.message 0))))
  refused "a named Error in a helper" (helperB (.xor 255) (.error (.named 0)))
  refused "an Error parameter in run" (siteA (.error .param))
  refused "an Error parameter in a closure" (withStep a 8
    (.closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .error .param} .add 3))
  refused "the accumulator in a closure" (withStep a 8
    (.closure {form := .require, cond := {word := .acc, test := .ne 1}, payload := .literal 8} .add 3))
  refused "a 33-byte revertLit" (siteA (.literal 7))
  admitted "a 32-byte revertLit" (siteA (.literal 6))
  refused "a literal past the table" (withStep a 8
    (.closure {form := .require, cond := {word := .input, test := .ne 1}, payload := .literal 10} .add 3))
  refused "revertEmpty through require" (withStep b 10
    (.site {form := .require, cond := {word := .acc, test := .bits 7 5}, payload := .none}))
  refused "an order constant of 4" (testA (.gt 4))
  refused "an equality constant of 4" (testA (.eq 4))
  refused "a bit value above its mask" (testA (.bits 1 2))
  refused "a bit mask of 4" (testA (.bits 4 0))
  refused "a counter outside a loop" (withStep b 10
    (.site {form := .when, cond := {word := .counter, test := .bits 7 5}, payload := .none}))
  refused "a selector of a counter outside a loop" (withStep a 1 (.error (.helper 1 .counter)))
  let message := fun (value : Nat) => Step.site {quiet with payload := .error (.make (.message value))}
  refused "a message past 64 bytes" (plain [bytes, .action (.bytes (.concat (.value (.bytes 0)) (.zeros 1))), message 1, observe])
  admitted "a 64-byte message" (plain [bytes, .action (.bytes (.concat (.value (.bytes 0)) (.zeros 1))), message 0, observe])
  refused "a message of an undeclared value" (withStep a 2 (.error (.make (.message 3))))
  refused "a fourth Error variable" (plain ([bytes] ++ List.replicate 4 (.error (.make .empty)) ++ [.site quiet, observe]))
  admitted "three Error variables" (plain ([bytes] ++ List.replicate 3 (.error (.make .empty)) ++ [.site quiet, observe]))
  refused "a third pair" (plain ([bytes] ++ List.replicate 3 (.data (.pair (.make .empty) .input)) ++ [.site quiet, observe]))
  refused "a third sum" (plain ([bytes] ++ List.replicate 3 (.data (.inr .input)) ++ [.site quiet, observe]))
  refused "a third enum" (plain ([bytes] ++ List.replicate 3 (.data (.second .input)) ++ [.site quiet, observe]))
  admitted "two of each data value" (plain ([bytes] ++ List.replicate 2 (.data (.pair (.make .empty) .input)) ++
    List.replicate 2 (.data (.inr .input)) ++ List.replicate 2 (.data (.second .input)) ++ [.site quiet, observe]))
  refused "a third closure" (plain ([bytes] ++ List.replicate 3 (.closure quiet .add 3) ++ [.site quiet, observe]))
  refused "a third function value" (raising (List.replicate 3 call))
  admitted "two function values" (raising (List.replicate 2 call))
  refused "two loops" (plain [bytes, .loop 1 [.site quiet], .loop 1 [.site quiet], observe])
  admitted "a loop" (loop 1 [.site quiet])
  refused "a loop mask of 2" (loop 2 [.site quiet])
  refused "an empty loop" (loop 1 [])
  refused "a loop of four items" (loop 1 (List.replicate 4 (.site quiet)))
  refused "a loop that writes" (loop 1 [.action (.write (.bytes 0) (.literal 0) .input .byte .inline), .site quiet])
  refused "a loop that observes" (loop 1 [.action (.observe .add 3 (.bytes 0) .length), .site quiet])
  refused "a loop that names a value twice" (loop 1 [.action (.alias (.bytes 0)), .site quiet])
  refused "a slice" (plain [bytes, .action (.slice (.bytes 0) (.drop 0)), .site quiet, observe])
  refused "an array" (plain [bytes, .action (.array false [.input]), .site quiet, observe])
  refused "a hash" (plain [bytes, .site quiet, .action (.observe .add 3 (.bytes 0) .hash)])
  refused "an input position" (plain [bytes, .site quiet, .action (.observe .add 3 (.bytes 0) (.word (.input 0 32)))])
  refused "an application of a missing closure" (withStep a 9 (.apply 1 .input .xor 9))
  refused "a take of a missing sum" (withStep a 7
    (.take (.sum 1) {form := .when, cond := {word := .input, test := .gt 255}, payload := .error .param} .add 7))
  refused "a selector from a raise helper" (withStep a 1 (.error (.helper 0 (.xor 9))))
  refused "a message from a pick helper" (withStep b 2 (.error (.message 1 0)))
  refused "a pick of a missing Error" (withStep b 3 (.error (.pick 1 .input (.named 1) (.make .empty))))
  refused "a call of a pick helper" (withStep b 7 (.call 1 (.make .empty) .input true .add 3))
  refused "a call of a missing helper" (withStep b 7 (.call 3 (.make .empty) .input true .add 3))
  refused "a counter in a call" (withStep b 7 (.call 2 (.make .empty) .counter true .add 3))
  refused "an even call fold constant" (withStep b 7 (.call 2 (.make .empty) .input true .add 4))

private def shapeValues : List (String × List String) := [
  ("helpers", ["call", "make", "message", "pick", "raise"]),
  ("forms", ["require", "requireLiteral", "revertEmpty", "revertLit", "revertWithError"]),
  ("errors", ["empty", "message", "picked", "selector"]),
  ("contexts", ["call", "closure", "enum", "helper", "loop", "pair", "run", "sum"]),
  ("carriers", ["captured", "held", "inline", "loop", "passed", "value", "variable"]),
  ("declarations", ["made", "messaged", "picked", "variable"]),
  ("data", ["enum0", "enum1", "inl", "inr", "pair"]),
  ("tests", ["bits", "eq", "gt", "lt", "ne"]),
  ("words", ["acc", "constant", "counter", "input", "local"]),
  ("lengths", ["0", "1-31", "32", "33-63", "64"]),
  ("hazards", ["alias", "allocated", "written"]),
  ("steps", ["action", "apply", "call", "closure", "data", "error", "loop", "site", "take"])]

/-- Generation is deterministic, its accepted plans draw every shape within
1,000 seeds, it replays exactly and drops steps to fit a smaller budget. -/
private def generationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 1000 do
    let plan := generate (UInt64.ofNat (seed + 1))
    ensure (RevertData.planJson plan == RevertData.planJson (generate (UInt64.ofNat (seed + 1))))
      "generation is not deterministic"
    if let .ok checked := RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes then
      if (RevertData.inputSensitive checked fuel).isOk then
        for (dimension, values) in checked.plan.shapes do
          for value in values do
            ensure ((shapeValues.lookup dimension).any (·.contains value)) s!"unknown shape {dimension}:{value}"
            unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in shapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"1,000 seeds never drew {dimension}:{value}"
  let all ← cases (RevertData.generateCases (Seed.ofNat 1) RevertData.defaultNodes 64 64 fuel)
  ensure (all.size = 64) "generation from seed 1 did not return 64 cases"
  let mut reverted := 0
  for case in all do
    ensure ((← expect (RevertData.replayCase case fuel)) == case) "a generated case failed exact replay"
    let direct ← expect (case.getObjVal? "directCore")
    if (direct.getObjValAs? String "status").toOption == some "reverted" then reverted := reverted + 1
  ensure (reverted ≥ 16 && reverted ≤ 48) "fewer than a quarter of 64 generated cases reverted or returned"
  let seeded ← cases (RevertData.generateCases (Seed.ofNat 7) RevertData.defaultNodes 12 4 fuel .seeded .nonIdentity)
  ensure (seeded.size = 12) "seeded generation did not return twelve inputs"
  for case in seeded do
    ensure ((← expect (RevertData.replayCase case fuel)) == case) "a seeded case failed exact replay"
  let mut dropped := false
  for seed in List.range 200 do
    if let .ok small := RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.minimumNodes then
      ensure (small.plan.nodes ≤ RevertData.minimumNodes) "a fitted plan exceeds its budget"
      if small.plan.steps.length < (generate (UInt64.ofNat (seed + 1))).steps.length then dropped := true
  ensure dropped "a 256-node budget never dropped a step"

/-- Which part of a site a reduction changed. -/
private def siteKind (before after : Site) : String :=
  if before.form != after.form then "require"
  else if before.payload != after.payload then "payload"
  else if before.cond.test != after.cond.test then "test"
  else "word"

/-- What a reduction changed, from the first helper or step that differs. -/
private def reductionKind (previous next : Plan) (inputChanged : Bool) : String :=
  if inputChanged then "input"
  else if next.helpers.length < previous.helpers.length then "helper"
  else if next.helpers != previous.helpers then
    match (previous.helpers.zip next.helpers).find? (fun (before, after) => before != after) with
    | some (.raise single fold constant, .raise single' fold' constant') =>
        if single != single' then siteKind single single' else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.pick test, .pick test') => if test != test' then "test" else "none"
    | some (.make _, .make _) | some (.call .., .call ..) => "constant"
    | _ => "none"
  else if next.steps.length < previous.steps.length then "step"
  else match (previous.steps.zip next.steps).find? (fun (before, after) => before != after) with
    | some (.call .., .site _) => "inline"
    | some (.call _ error word direct fold constant, .call _ error' word' direct' fold' constant') =>
        if direct != direct' then "form" else if error != error' then "argument"
        else if word != word' then "word" else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.error _, .error _) => "decl"
    | some (.data _, .data _) => "data"
    | some (.site single, .site single') => siteKind single single'
    | some (.take _ single fold constant, .take _ single' fold' constant')
    | some (.closure single fold constant, .closure single' fold' constant') =>
        if single != single' then siteKind single single' else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.apply _ word fold constant, .apply _ word' fold' constant') =>
        if word != word' then "word" else if fold != fold' || constant != constant' then "fold" else "none"
    | some (.loop mask body, .loop mask' body') =>
        if mask != mask' then "mask" else if body.length != body'.length then "body"
        else match (body.zip body').find? (fun (before, after) => before != after) with
          | some (.site single, .site single') => siteKind single single'
          | _ => "none"
    | _ => "none"

/-- Tampering is refused; reductions are admitted, strictly smaller and
replay, every kind applies, and a shrink response stays below its byte cap. -/
private def tamperChecks : IO Unit := do
  let all ← cases (RevertData.generateCases (Seed.ofNat 1) RevertData.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← expect (case.getObjVal? "revertDataPlan")
  ensure (RevertData.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed source replayed"
  ensure (RevertData.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed reference replayed"
  ensure (errorOf (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-revert-data-v0"))) fuel) == some "generatorVersion changed")
    "a changed generator version replayed"
  ensure (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "revertDataShapes" (Json.mkObj []))) fuel matches .error _) "changed revert data shapes replayed"
  ensure (RevertData.replayCase (case.setObjVal! "revertDataPlan" (plan.setObjVal! "steps" (.arr #[]))) fuel
    matches .error _) "a plan without steps replayed"
  ensure (RevertData.replayCase (case.setObjVal! "schema" (toJson "solcore-lean.semantic-revert-data-case.v0")) fuel
    matches .error _) "a changed case schema replayed"
  ensure (RevertData.replayCase (case.setObjVal! "directCore" (Json.mkObj [("stage", toJson "execution"),
      ("status", toJson "reverted"), ("output", toJson "0x00")])) fuel matches .ok _)
    "replay read the saved observation"
  let origin ← expect ((← provenance case).getObjVal? "origin")
  ensure (RevertData.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "2")))) fuel matches .error _) "a changed seed replayed"
  let fixture := RevertData.planJson fixtureA
  let some fixtureChecked := RevertData.CheckedPlan.ofPlan? fixtureA
    | throw (IO.userError "the first fixture failed the checker")
  let fixtureCase := RevertData.makeCase fixtureChecked (Word.ofNatModulo 5)
    (RevertData.emit fixtureA) (Json.mkObj [("kind", toJson "imported")]) fuel
  ensure ((← expect (RevertData.replayCase fixtureCase fuel)) == fixtureCase) "the imported fixture case failed replay"
  let helpers ← expect (fixture.getObjValAs? (Array Json) "helpers")
  let changed := helpers.set! 2 (RevertData.helperJson (.call 0 8))
  ensure (RevertData.replayCase (fixtureCase.setObjVal! "revertDataPlan" (fixture.setObjVal! "helpers" (.arr changed))) fuel
    matches .error _) "a changed helper replayed against the saved reference"
  let shrunk ← expect (RevertData.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated case"
  ensure (shrunk.compress.utf8ByteSize ≤ 2 * 1024 * 1024) "a shrink response exceeds 2 MiB"
  for candidate in reduced do
    ensure ((← expect (RevertData.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
  let parent ← expect (RevertData.caseProgram case)
  for reduction in RevertData.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a reduction is not strictly smaller"
  let mut kinds : List String := []
  let sources := [fixtureA, fixtureB].filterMap RevertData.CheckedPlan.ofPlan? ++ (List.range 40).filterMap fun seed =>
    (RevertData.generatedPlan (Seed.ofNat (seed + 1)) RevertData.defaultNodes).toOption
  for checked in sources do
    let source : RevertData.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
    for reduction in RevertData.reductions source do
      let kind := reductionKind checked.plan reduction.candidate.plan.plan (reduction.candidate.input != source.input)
      unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["step", "helper", "inline", "form", "argument", "word", "fold", "decl", "data", "payload", "require",
      "test", "constant", "mask", "body", "input"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in the fixtures and 40 plans"
  let reducedOrigin ← expect ((← provenance reduced[0]!).getObjVal? "origin")
  ensure (RevertData.replayCase (reduced[0]!.setObjVal! "provenance" ((← provenance reduced[0]!).setObjVal!
      "origin" (reducedOrigin.setObjVal! "parentPlan" (← expect (reduced[0]!.getObjVal? "revertDataPlan"))))) fuel
      matches .error _)
    "a reduction claiming itself as its parent replayed"

def testSourceRevertDataCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

/-! `runtime-halts`. Its reference returns the accumulator, or the revert data or
the halt of the first site whose condition decides, and agrees with the same
interpreter, which stops at a halt site; two fixtures' sources and results are
golden, the results from the corpus validator's Python model. Admission refuses
halts outside their forms and plans that reach none, and revert data plans
refuse halts; generation draws every halt shape and replays exactly; tampering
is refused, and reductions keep a halt, are strictly smaller and replay. -/

/-- The first fixture halts in a helper two helpers deep, through a function
value with a Yul `if`, in a closure through std.opcodes' `invalid()`, in a loop
and in `run` with inline Yul and `assert`, after a selector revert and before a
byte write and a literal revert. The second halts in the `Error` arms of a
pair, a sum and an enum, on the input, the accumulator and a constant, before
and after an empty revert. -/
private def haltFixtureA : Plan := {
  helpers := [
    .raise {form := .require, cond := {word := .input, test := .ne 0}, payload := .halt .assert} .add 3,
    .call 0 1,
    .raise {form := .when, cond := {word := .xor 5, test := .eq 0}, payload := .halt .yul} .xor 9],
  steps := [
    .action (.bytes (.toBytes (.word .input))),
    .site {form := .when, cond := {word := .input, test := .eq 2}, payload := .error (.make (.selector .input))},
    .site {form := .when, cond := {word := .input, test := .eq 255}, payload := .halt .inline},
    .action (.write (.bytes 0) (.literal 0) .input .byte .inline),
    .call 1 (.make .empty) .input true .add 3,
    .site {form := .require, cond := {word := .input, test := .lt 1000}, payload := .literal 3},
    .call 2 (.make .empty) (.add 2) false .xor 5,
    .closure {form := .when, cond := {word := .input, test := .bits 3 1}, payload := .halt .opcode} .add 7,
    .apply 0 (.add 7) .add 3,
    .loop 7 [.action (.bytes (.toBytes (.word .counter))),
      .site {form := .when, cond := {word := .counter, test := .eq 3}, payload := .halt .inline}],
    .site {form := .require, cond := {word := .acc, test := .ne 3}, payload := .halt .assert},
    .action (.observe .add 3 (.bytes 0) (.byte (.literal 0)))]}

private def haltFixtureB : Plan := {
  helpers := [],
  steps := [
    .error (.make .empty),
    .data (.pair (.named 0) (.add 1)),
    .data (.inl (.make (.selector .input))),
    .data (.first (.named 0) (.mul 3)),
    .take (.pair 0) {form := .require, cond := {word := .input, test := .ne 1}, payload := .halt .assert} .add 5,
    .take (.sum 0) {form := .when, cond := {word := .acc, test := .bits 7 3}, payload := .halt .yul} .add 3,
    .take (.enum 0) {form := .when, cond := {word := .input, test := .gt (2 ^ 255)}, payload := .halt .opcode} .xor 11,
    .site {form := .when, cond := {word := .input, test := .lt 1}, payload := .error (.named 0)},
    .site {form := .when, cond := {word := .xor 255, test := .eq 0}, payload := .halt .inline}]}

private def haltHeader : List String := [
  "import * from std;",
  "import * from std.dispatch;",
  "import { mload, mstore, mstore8, shr, mod, invalid } from std.opcodes;",
  ""]

/-- From the Python model of `Tests/scripts/test-semantic-revert-data-corpus.py`:
a returned Word in decimal, revert data in hex, a halt as `invalid`. -/
private def haltFixtureAResults : List (Nat × String) := [
  (0, "321"),
  (1, "217"),
  (2, "0x00000002"),
  (255, "invalid"),
  (256, "10305"),
  (2 ^ 256 - 1, "invalid"),
  (2 ^ 255, "0x746f6f206c61726765"),
  (2 ^ 255 - 1, "0x746f6f206c61726765"),
  (3, "invalid"),
  (5, "invalid"),
  (6, "invalid"),
  (1001, "0x746f6f206c61726765")]

private def haltFixtureASource : String := String.intercalate "\n" (haltHeader ++ [
  "function sc_byte<a>(sc_v: a, sc_i: word) returns (word) where a: MemorySize, a: MemoryPointer {",
  "    return shr(248, mload(MemoryPointer.ptr(truncate(slice_(sc_v, sc_i), 1))));",
  "}",
  "",
  "function sc_h0(sc_e: Error, sc_w: word) returns (word) {",
  "    assert((sc_w != 0));",
  "    return (sc_w + 3);",
  "}",
  "",
  "function sc_h1(sc_e: Error, sc_w: word) returns (word) {",
  "    return sc_h0(sc_e, (sc_w + 1));",
  "}",
  "",
  "function sc_h2(sc_e: Error, sc_w: word) returns (word) {",
  "    assembly {",
  "        if eq(xor(sc_w, 5), 0) {",
  "            invalid()",
  "        }",
  "    }",
  "    return (sc_w ^ 9);",
  "}",
  "",
  "contract SynthesizedHalts {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_b0: memory<bytes> = to_bytes(bytes32(sc_x));",
  "        if (sc_x == 2) {",
  "            revertWithError(Error(sc_x));",
  "        }",
  "        if (sc_x == 255) {",
  "            assembly {",
  "                invalid()",
  "            }",
  "        }",
  "        mstore8(MemoryPointer.ptr(truncate(slice_(sc_b0, 0), 1)), sc_x);",
  "        sc_r = ((sc_r * 3) + sc_h1(Error.Empty, sc_x));",
  "        require((sc_x < 1000), \"too large\");",
  "        let sc_f0: function (Error, word) returns (word) = sc_h2;",
  "        sc_r = ((sc_r * 5) ^ sc_f0(Error.Empty, (sc_x + 2)));",
  "        let sc_c0: function (word) returns (word) = lam (sc_j: word) -> word {",
  "            if ((sc_j & 3) == 1) {",
  "                invalid();",
  "            }",
  "            return (sc_j + 7);",
  "        };",
  "        sc_r = ((sc_r * 3) + sc_c0((sc_x + 7)));",
  "        let sc_limit: word = (sc_x & 7);",
  "        let sc_counter: word = 0;",
  "        while (sc_limit > sc_counter) {",
  "            let sc_b1: memory<bytes> = to_bytes(bytes32(sc_counter));",
  "            if (sc_counter == 3) {",
  "                assembly {",
  "                    invalid()",
  "                }",
  "            }",
  "            sc_counter = (sc_counter + 1);",
  "        }",
  "        assert((sc_r != 3));",
  "        sc_r = ((sc_r * 3) + sc_byte(sc_b0, 0));",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def haltFixtureAShapes : List (String × List String) := [
  ("halts", ["assert", "inline", "invalid", "yul"]),
  ("haltContexts", ["call", "closure", "helper", "loop", "run"]),
  ("haltTests", ["bits", "eq", "ne"]),
  ("haltWords", ["acc", "counter", "input", "local"]),
  ("haltOrders", ["revert-after", "revert-before", "write-after", "write-before"])]

private def haltFixtureBResults : List (Nat × String) := [
  (0, "0x"),
  (1, "invalid"),
  (2, "invalid"),
  (255, "invalid"),
  (256, "2059"),
  (2 ^ 256 - 1, "invalid"),
  (2 ^ 255, "11"),
  (2 ^ 255 - 1, "115792089237316195423570985008687907853269984665640564039457584007913129639933"),
  (3, "37"),
  (5, "77"),
  (6, "95"),
  (1001, "8373")]

private def haltFixtureBSource : String := String.intercalate "\n" (haltHeader ++ [
  "enum Sc_F {",
  "    Sc_F0(Error, word),",
  "    Sc_F1(word)",
  "}",
  "",
  "contract SynthesizedHalts {",
  "    function run(input: uint256) public returns (uint256) {",
  "        let sc_x: word = Typedef.rep(input);",
  "        let sc_r: word = 0;",
  "        let sc_e0: Error = Error.Empty;",
  "        let sc_t0: (Error, word) = (sc_e0, (sc_x + 1));",
  "        let sc_u0: sum<Error, word> = inl(Error(sc_x));",
  "        let sc_g0: Sc_F = Sc_F.Sc_F0(sc_e0, (sc_x * 3));",
  "        match (sc_t0) {",
  "            case (sc_e, sc_w) {",
  "                assert((sc_x != 1));",
  "                sc_r = ((sc_r * 5) + sc_w);",
  "            }",
  "        }",
  "        match (sc_u0) {",
  "            case inl(sc_e) {",
  "                assembly {",
  "                    if eq(and(sc_r, 7), 3) {",
  "                        invalid()",
  "                    }",
  "                }",
  "            }",
  "            case inr(sc_w) {",
  "                sc_r = ((sc_r * 3) + sc_w);",
  "            }",
  "        }",
  "        match (sc_g0) {",
  "            case Sc_F.Sc_F0(sc_e, sc_w) {",
  "                if (sc_x > 57896044618658097711785492504343953926634992332820282019728792003956564819968) {",
  "                    invalid();",
  "                }",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "            case Sc_F.Sc_F1(sc_w) {",
  "                sc_r = ((sc_r * 11) ^ sc_w);",
  "            }",
  "        }",
  "        if (sc_x < 1) {",
  "            revertWithError(sc_e0);",
  "        }",
  "        if ((sc_x ^ 255) == 0) {",
  "            assembly {",
  "                invalid()",
  "            }",
  "        }",
  "        return uint256(sc_r);",
  "    }",
  "}"]) ++ "\n"

private def haltFixtureBShapes : List (String × List String) := [
  ("halts", ["assert", "inline", "invalid", "yul"]),
  ("haltContexts", ["enum", "pair", "run", "sum"]),
  ("haltTests", ["bits", "eq", "gt", "ne"]),
  ("haltWords", ["acc", "constant", "input"]),
  ("haltOrders", ["revert-after", "revert-before"])]

private def haltFixtureChecks : IO Unit := do
  for (label, plan, source, results, shapes) in [
      ("first", haltFixtureA, haltFixtureASource, haltFixtureAResults, haltFixtureAShapes),
      ("second", haltFixtureB, haltFixtureBSource, haltFixtureBResults, haltFixtureBShapes)] do
    ensure plan.haltAdmitted s!"the {label} halt fixture plan is not admitted"
    ensure (!plan.admitted) s!"the {label} halt fixture plan is admitted as a revert data plan"
    let some checked := Halts.CheckedPlan.ofPlan? plan
      | throw (IO.userError s!"the {label} halt fixture failed the checker")
    ensure ((Halts.emit plan).source == source) s!"the {label} halt fixture source changed"
    for (value, expected) in results do
      ensure ((← run (checked.program (Word.ofNatModulo value))).text == expected)
        s!"{label} halt fixture input {value}: Core result"
      ensure ((interpret plan value).map Result.text == some expected) s!"{label} halt fixture input {value}: interpreter result"
    ensure (plan.haltShapes == shapes) s!"the {label} halt fixture shapes changed"
    ensure (match Halts.checkedPlan (Halts.planJson plan) with
      | .ok decoded => decoded.plan == plan
      | .error _ => false) s!"the {label} halt fixture plan JSON does not round-trip"
    ensure (RevertData.checkedPlan (RevertData.planJson plan) matches .error _)
      s!"the {label} halt fixture plan is checked as a revert data plan"
  ensure (Halts.checkedPlan (Halts.planJson fixtureA) matches .error _) "a revert data plan is checked as a halt plan"
  let some first := Halts.CheckedPlan.ofPlan? haltFixtureA
    | throw (IO.userError "the first halt fixture failed the checker")
  ensure (Halts.observe first (Word.ofNatModulo 255) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "invalid")]) "a halt is not observed as INVALID's"
  ensure (Halts.observe first (Word.ofNatModulo 2) fuel == Json.mkObj [("stage", toJson "execution"),
    ("status", toJson "reverted"), ("output", toJson "0x00000002")]) "a revert of a halt plan lost its data"

/-- Admission refuses a halt outside its forms and a plan that reaches no halt. -/
private def haltAdmissionChecks : IO Unit := do
  let refused := fun (label : String) (plan : Plan) => ensure (!plan.haltAdmitted) s!"admitted the halt plan with {label}"
  let admitted := fun (label : String) (plan : Plan) => ensure plan.haltAdmitted s!"refused the halt plan with {label}"
  let b := haltFixtureB
  let halting := fun (form : Form) (halt : Halt) =>
    ({form, cond := {word := .input, test := .eq 0}, payload := .halt halt} : Site)
  let quiet : Site := {form := .when, cond := {word := .input, test := .eq 1}, payload := .none}
  let bytes := Step.action (.bytes (.toBytes (.word .input)))
  let observe := Step.action (.observe .add 3 (.bytes 0) .length)
  admitted "a halt and an observation" {helpers := [], steps := [bytes, .site (halting .when .inline), observe]}
  refused "an assert under if" (withStep b 8 (.site (halting .when .assert)))
  for halt in [Halt.opcode, .inline, .yul] do
    refused s!"{halt.name} through require" (withStep b 8 (.site (halting .require halt)))
    admitted s!"{halt.name} under if" (withStep b 8 (.site (halting .when halt)))
  admitted "assert through require" (withStep b 8 (.site (halting .require .assert)))
  let unhalted : Plan := {b with steps := b.steps.take 4 ++
    [.take (.pair 0) {form := .require, cond := {word := .input, test := .ne 1}, payload := .error .param} .add 5,
     b.steps[7]!]}
  refused "no halt" unhalted
  ensure unhalted.admitted "a revert data plan without a halt is refused"
  refused "a halt only in a closure never applied"
    {helpers := [], steps := [bytes, .closure (halting .when .inline) .add 3, .site quiet, observe]}
  admitted "a halt in an applied closure"
    {helpers := [], steps := [bytes, .closure (halting .when .inline) .add 3, .apply 0 .input .add 3]}
  refused "a halt only in the Error arm of a sum holding a Word"
    {helpers := [], steps := [.data (.inr .input), .take (.sum 0) (halting .when .yul) .add 3, .site quiet]}
  refused "a halt only in a helper nothing calls"
    {helpers := [.raise (halting .when .yul) .add 3], steps := [bytes, .site quiet, observe]}
  admitted "a halt in a called helper"
    {helpers := [.raise (halting .when .yul) .add 3], steps := [.call 0 (.make .empty) .input true .add 3]}
  let counted : Site := {form := .when, cond := {word := .counter, test := .eq 2}, payload := .halt .yul}
  refused "a halt on a counter outside a loop" {helpers := [], steps := [bytes, .site counted, observe]}
  admitted "a loop halting on its counter" {helpers := [], steps := [bytes, .loop 3 [.site counted], observe]}

/-- The reference agrees with the interpreter on 200 generated halt plans at
the eight boundary inputs and four others. -/
private def haltModelChecks : IO Unit := do
  let mut compared := 0
  let mut halted := 0
  let mut reverted := 0
  for seed in List.range 200 do
    match Halts.generatedPlan (Seed.ofNat (seed + 1)) Halts.defaultNodes with
    | .error _ => pure ()
    | .ok checked =>
        for input in boundary ++ [3, 1001, 0x1234567890abcdef, 2 ^ 200 + 77] do
          let core ← run (checked.program (Word.ofNatModulo input))
          ensure (interpret checked.plan input == some core)
            s!"halt seed {seed + 1} input {input}: the reference differs from the interpreter"
          compared := compared + 1
          match core with
          | .halted => halted := halted + 1
          | .reverted _ => reverted := reverted + 1
          | .returned _ => pure ()
  ensure (compared = 2400) "a generated halt plan failed admission or the checker"
  ensure (halted ≥ 500 && reverted ≥ 500 && compared - halted - reverted ≥ 1000)
    "fewer than 500 compared outcomes halted or reverted, or 1,000 returned"

private def haltShapeValues : List (String × List String) := [
  ("halts", ["assert", "inline", "invalid", "yul"]),
  ("haltContexts", ["call", "closure", "enum", "helper", "loop", "pair", "run", "sum"]),
  ("haltTests", ["bits", "eq", "gt", "lt", "ne"]),
  ("haltWords", ["acc", "constant", "counter", "input", "local"]),
  ("haltOrders", ["revert-after", "revert-before", "write-after", "write-before"])]

/-- Generation is deterministic, its accepted plans draw every halt shape
within 500 seeds, it replays exactly and drops steps to fit a smaller
budget. -/
private def haltGenerationChecks : IO Unit := do
  let mut seen : List (String × String) := []
  for seed in List.range 500 do
    let plan := generateHalts (UInt64.ofNat (seed + 1))
    ensure (Halts.planJson plan == Halts.planJson (generateHalts (UInt64.ofNat (seed + 1))))
      "halt generation is not deterministic"
    if let .ok checked := Halts.generatedPlan (Seed.ofNat (seed + 1)) Halts.defaultNodes then
      if (Halts.inputSensitive checked fuel).isOk then
        for (dimension, values) in checked.plan.haltShapes do
          for value in values do
            ensure ((haltShapeValues.lookup dimension).any (·.contains value)) s!"unknown halt shape {dimension}:{value}"
            unless seen.contains (dimension, value) do seen := (dimension, value) :: seen
  for (dimension, values) in haltShapeValues do
    for value in values do
      ensure (seen.contains (dimension, value)) s!"500 seeds never drew {dimension}:{value}"
  let all ← cases (Halts.generateCases (Seed.ofNat 1) Halts.defaultNodes 64 64 fuel)
  ensure (all.size = 64) "halt generation from seed 1 did not return 64 cases"
  let mut halted := 0
  for case in all do
    ensure ((← expect (Halts.replayCase case fuel)) == case) "a generated halt case failed exact replay"
    let direct ← expect (case.getObjVal? "directCore")
    if (direct.getObjValAs? String "status").toOption == some "invalid" then halted := halted + 1
  ensure (halted ≥ 16 && halted ≤ 48) "fewer than a quarter of 64 generated halt cases halted or did not"
  let seeded ← cases (Halts.generateCases (Seed.ofNat 7) Halts.defaultNodes 12 4 fuel .seeded)
  ensure (seeded.size = 12) "seeded halt generation did not return twelve inputs"
  for case in seeded do
    ensure ((← expect (Halts.replayCase case fuel)) == case) "a seeded halt case failed exact replay"
  let mut dropped := false
  for seed in List.range 200 do
    if let .ok small := Halts.generatedPlan (Seed.ofNat (seed + 1)) Halts.minimumNodes then
      ensure (small.plan.nodes ≤ Halts.minimumNodes) "a fitted halt plan exceeds its budget"
      ensure small.plan.haltAdmitted "a fitted halt plan reaches no halt"
      if small.plan.steps.length < (generateHalts (UInt64.ofNat (seed + 1))).steps.length then dropped := true
  ensure dropped "a 256-node budget never dropped a step of a halt plan"

/-- Tampering is refused; reductions reach a halt, are strictly smaller and
replay, and a halt through std.opcodes or a Yul `if` lowers to inline Yul. -/
private def haltTamperChecks : IO Unit := do
  let all ← cases (Halts.generateCases (Seed.ofNat 1) Halts.defaultNodes 8 4 fuel)
  let case := all[0]!
  let plan ← expect (case.getObjVal? "haltPlan")
  ensure (Halts.replayCase (case.setObjVal! "source" (toJson "contract C {}")) fuel matches .error _)
    "a changed halt source replayed"
  ensure (Halts.replayCase (case.setObjVal! "program" (Solcore.Core.Wire.encodeProgram
      {resultType := .word, dataDefinitions := [], body := .word Word.zero})) fuel matches .error _)
    "a changed halt reference replayed"
  ensure (errorOf (Halts.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "generatorVersion" (toJson "core-halt-v0"))) fuel) == some "generatorVersion changed")
    "a changed halt generator version replayed"
  ensure (Halts.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "haltShapes" (Json.mkObj []))) fuel matches .error _) "changed halt shapes replayed"
  ensure (Halts.replayCase (case.setObjVal! "haltPlan" (plan.setObjVal! "steps" (.arr #[]))) fuel
    matches .error _) "a halt plan without steps replayed"
  ensure (Halts.replayCase (case.setObjVal! "schema" (toJson RevertData.caseSchema)) fuel matches .error _)
    "a halt case replayed as a revert data case"
  ensure (Halts.replayCase (case.setObjVal! "directCore" (Json.mkObj [("stage", toJson "execution"),
      ("status", toJson "returned"), ("word", toJson "0")])) fuel matches .ok _)
    "halt replay read the saved observation"
  let origin ← expect ((← provenance case).getObjVal? "origin")
  ensure (Halts.replayCase (case.setObjVal! "provenance" ((← provenance case).setObjVal!
      "origin" (origin.setObjVal! "seed" (toJson "4")))) fuel matches .error _) "a changed halt seed replayed"
  let shrunk ← expect (Halts.shrinkCases case 4096 fuel)
  let reduced ← cases shrunk
  ensure (!reduced.isEmpty) "no reduction of the first generated halt case"
  for candidate in reduced do
    ensure ((← expect (Halts.replayCase candidate fuel)) == candidate) "a halt reduction failed exact replay"
  let parent ← expect (Halts.caseProgram case)
  for reduction in Halts.reductions parent do
    ensure (decide (reduction.candidate.measure.StrictlySmaller parent.measure)) "a halt reduction is not strictly smaller"
    ensure reduction.candidate.plan.plan.haltAdmitted "a halt reduction reaches no halt"
  let mut kinds : List String := []
  let sources := [haltFixtureA, haltFixtureB].filterMap Halts.CheckedPlan.ofPlan? ++ (List.range 40).filterMap fun seed =>
    (Halts.generatedPlan (Seed.ofNat (seed + 1)) Halts.defaultNodes).toOption
  for checked in sources do
    let source : Halts.CheckedInput := ⟨checked, Word.ofNatModulo 5⟩
    for reduction in Halts.reductions source do
      let kind := reductionKind checked.plan reduction.candidate.plan.plan (reduction.candidate.input != source.input)
      unless kinds.contains kind do kinds := kind :: kinds
  for kind in ["step", "helper", "inline", "form", "word", "fold", "payload", "test", "mask", "body", "input"] do
    ensure (kinds.contains kind) s!"no {kind} reduction in the halt fixtures and 40 plans"
  let some fixture := Halts.CheckedPlan.ofPlan? haltFixtureA
    | throw (IO.userError "the first halt fixture failed the checker")
  let lowered := (Halts.reductions ⟨fixture, Word.ofNatModulo 5⟩).any fun reduction =>
    reduction.candidate.plan.plan.helpers[2]? == some (.raise
      {form := .when, cond := {word := .xor 5, test := .eq 0}, payload := .halt .inline} .xor 9)
  ensure lowered "a Yul if halt did not lower to inline Yul"

def testSourceHaltCases : IO Unit := do
  haltFixtureChecks
  haltAdmissionChecks
  haltModelChecks
  haltGenerationChecks
  haltTamperChecks

end Tests.SourceRevertDataCases
end
