import Solcore.Synthesis.Source.CallValueCases

/-! Call-value case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction, value and plan boundaries,
the funding bounds and typed scenario reductions over steps, transactions,
inputs, values, flags and the deployment value. Expected values here are test
goldens only; emitted cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceCallValueCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.CallValue (CheckedPlan)
open Solcore.Synthesis.Stateful.CallValueExecution (Transaction Bindings)

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

private def makePlan (body : Wire.Expr) (deployment : Nat) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] entry |
    throw (IO.userError "call-value fixture failed step admission")
  let some plan := CheckedPlan.ofParts? graph (Word.ofNatModulo deployment) |
    throw (IO.userError "call-value wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((flags, input, value), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input, Word.ofNatModulo value⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO CallValue.CheckedScenario :=
  get (CallValue.checkedScenario plan (transactions values))
private def imported (value : CallValue.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (CallValue.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0) 5
  let value ← scenario identity [(0, 5, 2 ^ 64), (3, 1, 7), (2, 2 ^ 255, 0)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1"] : List String)) "call-value case changed its observed slots"
  ensure ((← field saved "callValuePlan") == CallValue.planJson identity) "call-value case lost its deployment value"
  ensure ((← get (CallValue.replayCase saved 10000)) == saved) "imported call-value case did not replay"
  ensure ((← get (CallValue.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "call-value replay consumed a stored expected result"
  let changed ← imported (← scenario (← makePlan (.var 0) 0) [(1, 3, 2 ^ 70)])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "flags, inputs, values or the deployment value were substituted into source or Core code"
  let observed := CallValue.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "call-value scenario did not follow its flags parities"
  ensure (((← rows observed).map fun row => (row.getObjValAs? String "committedBalance").toOption) ==
      #[some (toString (2 ^ 64 + 5)), some (toString (2 ^ 64 + 5)), some (toString (2 ^ 64 + 5))])
    "committed balances did not accept, refund and accept zero"
  ensure ((← get (CallValue.checkBalances value observed)) == ["returned", "reverted", "returned"])
    "the balance self-check rejected a correct history"
  let rebound ← rows (CallValue.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent call-value profile changed with bindings"
  let forged := observed.setObjVal! "transactions" (toJson ((← rows observed).set! 1
    ((← rows observed)[1]!.setObjVal! "committedBalance" (toJson (toString (2 ^ 64 + 12))))))
  rejected (CallValue.checkBalances value forged) "the balance self-check accepted a committed refund"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 12 do
    let choices := CallValue.sequenceChoices (Seed.ofNat seed)
    let bounds := [6, 6, 6, 6, 6, 6, 2, 4]
    ensure (choices.length == bounds.length && (choices.zip bounds).all fun (value, bound) => value < bound)
      "sequence choices escaped their banks"
    match CallValue.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3 &&
          CallValue.deploymentBank.contains value.plan.deploymentValue)
          "call-value recipe lost node/transaction/helper/deployment bounds"
        ensure (value.transactions.all fun tx => CallValue.boundaryInputs.contains tx.input &&
          CallValue.valueBank.contains tx.value && tx.flags.val < 2) "generated input, value or flags escaped its bank"
        ensure ((value.transactions.map CallValue.reverts) == CallValue.generatedParities (Seed.ofNat seed))
          "generated flags lost their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (CallValue.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (CallValue.generatedScenario (Seed.ofNat 0) CallValue.programOverhead) "undersized node budget accepted"
  let corpus := CallValue.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == CallValue.generateCases (Seed.ofNat 0) 384 4 512 10000) "call-value generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "call-value count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (CallValue.replayCase saved 10000)) == saved) "generated call-value provenance did not replay"
    let low ← get (CallValue.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := CallValue.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "call-value generation resource exhaustion was not distinguished"
  ensure ((← rows (CallValue.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (CallValue.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (CallValue.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "call-value generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "02"),
      ("flags", toJson (toString (2 ^ 256))), ("input", toJson "05"), ("input", toJson "7"),
      ("value", toJson "07"), ("value", toJson (toString (2 ^ 256))), ("calldata", toJson "0x"), ("extra", toJson true)] do
    rejected (CallValue.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical call-value transaction accepted"
  rejected (CallValue.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (CallValue.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  let plan ← makePlan (.var 0) 5
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 1), (0, 0, 1)] |>.map fun tx => {tx with id := "same"}))
    "duplicate transaction IDs accepted"
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 2 ^ 70 + 1)])) "a value above 2^70 accepted"
  rejected (CallValue.checkedScenario plan (transactions [(0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70)]))
    "more than three transactions accepted"
  -- Four values of at most 2^70 reach the 2^72 total exactly; the bound is attainable.
  let atBound ← get (CallValue.checkedScenario (← makePlan (.var 0) (2 ^ 70))
    (transactions [(0, 0, 2 ^ 70), (0, 0, 2 ^ 70), (0, 0, 2 ^ 70)]))
  ensure (CallValue.totalValue atBound.plan.deploymentValue atBound.transactions == CallValue.maxTotal)
    "the funding total at the value bounds changed"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("callValuePlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (CallValue.caseProgram (saved.setObjVal! name bad)) "invalid call-value case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (CallValue.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered call-value provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (CallValue.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated call-value recipe accepted"
  let planJson ← field saved "callValuePlan"
  rejected (CallValue.checkedPlan (planJson.setObjVal! "extra" Json.null)) "noncanonical call-value plan accepted"
  rejected (CallValue.checkedPlan (planJson.setObjVal! "schema" (toJson "solcore-lean.log-plan.v1")))
    "log plan schema accepted as a call-value plan"
  for bad in [toJson "05", toJson (toString (2 ^ 70 + 1)), toJson (5 : Nat), Json.null] do
    rejected (CallValue.checkedPlan (planJson.setObjVal! "deploymentValue" bad)) "invalid deployment value accepted"
  rejected (CallValue.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (CallValue.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "name" (toJson "SynthesizedLogs"))) 10000)
    "log wrapper metadata accepted for the call-value profile"
  rejected (CallValue.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-log-case.v1")) 10000)
    "log case schema accepted by the call-value tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2)) 5
  let value ← scenario plan [(2 ^ 255 + 3, 2 ^ 256 - 1, 2 ^ 70), (6, 7, 2 ^ 64), (1, 2 ^ 255, 7)]
  let saved ← imported value
  let candidates ← get (CallValue.shrinkCases saved 1000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (CallValue.shrinkCases saved 1000 10000)))
    "call-value reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut loweredValue := false
  let mut reducedFlags := false
  let mut zeroDeployment := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (CallValue.caseProgram row)
    ensure (decide (CallValue.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "call-value reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("plan", CallValue.planJson reduced.plan),
      ("transactions", CallValue.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate call-value reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let sameCount := reduced.transactions.length == value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    loweredValue := loweredValue || (sameCount && pairs.any fun (left, right) =>
      left.value.val < right.value.val && CallValue.valueBank.contains left.value)
    reducedFlags := reducedFlags || (sameCount && pairs.any fun (left, right) =>
      left.flags.val < right.flags.val && left.flags.bitAnd right.flags == left.flags)
    zeroDeployment := zeroDeployment || (reduced.plan.deploymentValue == Word.zero)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (CallValue.replayCase row 10000)) == row) "reduced call-value case did not replay"
  ensure (removed && loweredInput && loweredValue && reducedFlags && zeroDeployment && changedStep)
    "call-value shrink omitted sequence/input/value/flags/deployment/step axes"
  ensure ((← rows (← get (CallValue.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (CallValue.shrinkCases saved 0 10000)) "cases").isEmpty) "call-value shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (CallValue.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", CallValue.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", CallValue.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (CallValue.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict call-value reduction provenance accepted"

def testSourceCallValueCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceCallValueCases
