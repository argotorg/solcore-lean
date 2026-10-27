import Solcore.Synthesis.Source.EventLogCases

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
