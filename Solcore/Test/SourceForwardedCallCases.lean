import Solcore.Synthesis.Source.ForwardedCallCases

/-! Forwarded-value case regressions: exact replay, bounded generation from an
independent sequence stream, canonical transaction boundaries, the forwarding
protocol check and typed reductions over steps, transactions, inputs, revert
bits, call values and amounts. Expected values here are test goldens only;
cases and the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceForwardedCallCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.ForwardedCall (CheckedPlan)
open Solcore.Synthesis.Stateful.ForwardedCallExecution (Transaction Bindings)

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
private def bindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "forwarded-value fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "forwarded-value wrappers failed host admission")
  return plan
private def transactions (values : List (Nat × Nat × Nat)) : List Transaction :=
  values.zipIdx.map fun ((input, value, amount), index) =>
    ⟨"call-" ++ toString index, Word.ofNatModulo input, Word.ofNatModulo value, Word.ofNatModulo amount⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × Nat × Nat)) : IO ForwardedCall.CheckedScenario :=
  get (ForwardedCall.checkedScenario plan (transactions values))
private def imported (value : ForwardedCall.CheckedScenario) (fuel : Nat := 100000) : IO Json :=
  get (ForwardedCall.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, 7, 5), (1, 0, 2 ^ 70), (2, 1, 1)]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1"] : List String)) "case did not declare slots zero and one"
  ensure ((← get (ForwardedCall.replayCase saved 100000)) == saved) "imported forwarded-value case did not replay"
  ensure ((← get (ForwardedCall.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 100000)) == saved)
    "forwarded-value replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, 2 ^ 64, 0), (2, 0, 7)])
  ensure ((← field saved "programs") == (← field changed "programs") &&
    (← string saved "source") == (← string changed "source"))
    "inputs, values or amounts were substituted into source or Core code"
  let observed := ForwardedCall.observe value bindings 100000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "returned", some "reverted"])
    "forwarded-value scenario did not follow its root parities"
  ensure ((← get (ForwardedCall.checkProtocol value observed)) == ["returned", "returned", "reverted"])
    "forwarded-value history broke its refund or balance protocol"
  -- A committed child or a moved balance breaks the protocol check.
  let observedRows ← rows observed
  let accounts ← get ((← field observedRows[1]! "committedAccounts").getArr?)
  let changedAccounts := accounts.map fun account =>
    if (account.getObjValAs? String "role").toOption == some "child" then account.setObjVal! "balance" (toJson "6") else account
  let forgedRow := observedRows[1]!.setObjVal! "committedAccounts" (.arr changedAccounts)
  let forged := observed.setObjVal! "transactions" (.arr (observedRows.set! 1 forgedRow))
  rejected (ForwardedCall.checkProtocol value forged) "a child account changed by a reverted child passed the protocol"
  ensure ((← rows (ForwardedCall.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩⟩ 100000)).map
      (fun row => (row.getObjVal? "output").toOption) == observedRows.map (fun row => (row.getObjVal? "output").toOption))
    "address-independent forwarded-value outcomes changed with bindings"
  rejected (ForwardedCall.checkedScenario identity (transactions [(0, 2 ^ 70 + 1, 0)])) "call value above 2^70 accepted"
  rejected (ForwardedCall.checkedScenario identity (transactions [(0, 0, 2 ^ 70 + 1)])) "amount above 2^70 accepted"
  ensure (ForwardedCall.modeInput (Word.ofNatModulo 6) 1 == Word.ofNatModulo 5 &&
    ForwardedCall.modeInput Word.maximum 0 == Word.ofNatModulo (2 ^ 256 - 4)) "call modes do not replace the low two bits"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := ForwardedCall.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 12 && (choices.zip ForwardedCall.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    match ForwardedCall.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && ForwardedCall.combinedNodes value.plan.step ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "forwarded-value recipe lost node/transaction/helper bounds"
        ensure (value.transactions.map (fun tx => tx.input.val % 4) == (choices.drop 3).take 3)
          "generated call modes escaped their draws"
        ensure (value.transactions.all fun tx => ForwardedCall.valueBank.contains tx.value && ForwardedCall.valueBank.contains tx.amount)
          "generated value or amount escaped its bank"
        ensure (value.transactions.all fun tx => ForwardedCall.boundaryInputs.any fun input =>
            ForwardedCall.modeInput input (tx.input.val % 4) == tx.input)
          "generated input is not a bank input with a call mode"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (ForwardedCall.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (ForwardedCall.generatedScenario (Seed.ofNat 0) ForwardedCall.programOverhead) "undersized node budget accepted"
  let corpus := ForwardedCall.generateCases (Seed.ofNat 0) 384 4 512 100000
  ensure (corpus == ForwardedCall.generateCases (Seed.ofNat 0) 384 4 512 100000) "forwarded-value generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "forwarded-value count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (ForwardedCall.replayCase saved 100000)) == saved) "generated forwarded-value provenance did not replay"
    let low ← get (ForwardedCall.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := ForwardedCall.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "forwarded-value generation resource exhaustion was not distinguished"
  ensure ((← rows (ForwardedCall.generateCases (Seed.ofNat seed) 384 2 1 100000) "cases").size == 1 &&
    (← natural (ForwardedCall.generateCases (Seed.ofNat seed) 384 0 10 100000) "attempted") == 0 &&
    (← rows (ForwardedCall.generateCases (Seed.ofNat seed) 384 1 0 100000) "cases").isEmpty)
    "forwarded-value generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("input", toJson "01"),
      ("input", toJson (toString (2 ^ 256))), ("value", toJson "07"), ("value", toJson (toString (2 ^ 70 + 1))),
      ("amount", toJson "05"), ("amount", toJson (toString (2 ^ 70 + 1))), ("amount", Json.null),
      ("target", toJson "child"), ("callee", toJson "parent"), ("calldata", toJson "0x"), ("extra", toJson true)] do
    rejected (ForwardedCall.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical forwarded-value transaction accepted"
  rejected (ForwardedCall.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (ForwardedCall.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (ForwardedCall.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  let initial ← field saved "initialState"
  for (name, bad) in [("initialState", initial.setObjVal! "callerBalance" (toJson "0")),
      ("initialState", Json.mkObj [("accounts", toJson ([] : List Json))]),
      ("observedSlots", toJson (["0"] : List String)), ("executionFuel", toJson (10000001 : Nat)),
      ("forwardPlan", Json.null), ("programs", Json.mkObj [("parent", Json.null), ("child", Json.null)])] do
    rejected (ForwardedCall.caseProgram (saved.setObjVal! name bad)) "invalid forwarded-value case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (ForwardedCall.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 100000)
      "tampered forwarded-value provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (ForwardedCall.replayCase (withOrigin (origin.setObjVal! name bad)) 100000)
      "tampered generated forwarded-value recipe accepted"
  let generatedRows ← rows generated
  rejected (ForwardedCall.replayCase (generated.setObjVal! "transactions"
      (.arr (generatedRows.set! 0 (generatedRows[0]!.setObjVal! "amount" (toJson "0"))))) 100000)
    "generated amount replaced without its seed"
  let plan ← field saved "forwardPlan"
  rejected (ForwardedCall.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical forwarded-value plan accepted"
  rejected (ForwardedCall.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.call-plan.v1")))
    "call plan schema accepted as a forwarded-value plan"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "source" (toJson "stale")) 100000) "stale source accepted"
  let contracts ← field saved "contracts"
  let parent ← field contracts "parent"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "contracts" (contracts.setObjVal! "parent"
      (parent.setObjVal! "constructorValue" (toJson "8")))) 100000)
    "the nested-call endowment accepted for the forwarding parent"
  rejected (ForwardedCall.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-call-case.v1")) 100000)
    "nested-call case schema accepted by the forwarded-value tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(7, 2 ^ 70, 2 ^ 64), (5, 7, 2 ^ 64 - 1), (2 ^ 255, 2 ^ 64, 2 ^ 70)]
  let saved ← imported value
  let candidates ← get (ForwardedCall.shrinkCases saved 2000 100000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (ForwardedCall.shrinkCases saved 2000 100000)))
    "forwarded-value reductions were empty or nondeterministic"
  let mut removed := false
  let mut loweredInput := false
  let mut clearedRevert := false
  let mut loweredValue := false
  let mut loweredAmount := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (ForwardedCall.caseProgram row)
    ensure (decide (ForwardedCall.StrictlySmaller reduced value) && reduced.plan.childProgram.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "forwarded-value reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("programs", ForwardedCall.programsJson reduced.plan),
      ("transactions", ForwardedCall.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate forwarded-value reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    loweredInput := loweredInput || (sameCount && pairs.any fun (left, right) => left.input.val < right.input.val)
    clearedRevert := clearedRevert || (sameCount && pairs.any fun (left, right) =>
      left.input.val + 1 == right.input.val || left.input.val + 2 == right.input.val)
    loweredValue := loweredValue || (sameCount && pairs.any fun (left, right) => left.value.val < right.value.val)
    loweredAmount := loweredAmount || (sameCount && pairs.any fun (left, right) => left.amount.val < right.amount.val)
    changedStep := changedStep || ForwardedCall.programsJson reduced.plan != ForwardedCall.programsJson value.plan
    ensure ((← get (ForwardedCall.replayCase row 100000)) == row) "reduced forwarded-value case did not replay"
  ensure (removed && loweredInput && clearedRevert && loweredValue && loweredAmount && changedStep)
    "forwarded-value shrink omitted sequence/input/revert/value/amount/step axes"
  ensure ((← rows (← get (ForwardedCall.shrinkCases saved 2 100000)) "cases") == result.extract 0 2 &&
    (← rows (← get (ForwardedCall.shrinkCases saved 0 100000)) "cases").isEmpty) "forwarded-value shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (ForwardedCall.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", ForwardedCall.planJson reduced.plan),
    ("parentPrograms", ForwardedCall.programsJson reduced.plan),
    ("parentTransactions", ForwardedCall.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (ForwardedCall.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 100000)
    "non-strict forwarded-value reduction provenance accepted"

def testSourceForwardedCallCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceForwardedCallCases
