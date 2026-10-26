import Solcore.Synthesis.Source.DynamicBytesCases

/-! Bytes case regressions: exact replay, bounded generation from an
independent sequence stream, canonical payload and calldata boundaries, and
typed reductions over steps, transactions, payload lengths, payload bytes and
flags. Expected values here are test goldens only; cases and the observer never
consume them. -/
set_option autoImplicit false

namespace Tests.SourceDynamicBytesCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicBytesExecution (Transaction Bindings)

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
private def ones (length : Nat) : List UInt8 := List.replicate length 0xff

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "bytes fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "bytes wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × List UInt8)) : List Transaction :=
  values.zipIdx.map fun ((flags, payload), index) => ⟨"call-" ++ toString index, Word.ofNatModulo flags, payload⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List UInt8)) : IO DynamicBytes.CheckedScenario :=
  get (DynamicBytes.checkedScenario plan (transactions values))
private def imported (value : DynamicBytes.CheckedScenario) (fuel : Nat := 10000) : IO Json :=
  get (DynamicBytes.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, [1, 3, 7]), (1, ones 33), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson (["0", "1", "2", "3", "4"] : List String))
    "case did not declare slots zero through four"
  ensure ((← get (DynamicBytes.replayCase saved 10000)) == saved) "imported bytes case did not replay"
  ensure ((← get (DynamicBytes.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 10000)) == saved)
    "bytes replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, []), (2, [9, 9])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "payloads or flags were substituted into source or Core code"
  ensure (((← rows saved).map fun row => (row.getObjValAs? String "payload").toOption) ==
      #[some "0x010307", some ("0x" ++ String.join (List.replicate 33 "ff")), some "0x"])
    "payloads are not canonical lowercase hexadecimal"
  let observed := DynamicBytes.observe value bindings 10000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "bytes scenario did not follow its flags parities"
  ensure ((← get (DynamicBytes.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "bytes history broke its length, last-byte or sum protocol"
  ensure ((← rows (DynamicBytes.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 10000)) == (← rows observed))
    "address-independent bytes profile changed with bindings"
  rejected (DynamicBytes.checkedScenario identity (transactions [(0, List.replicate 65 1)])) "65-byte payload accepted"
  ensure (DynamicBytes.tailByte [] == 0 && DynamicBytes.tailByte [1, 2, 0x80] == 0x80 &&
    [0, 1, 32, 33, 64].map (fun length => DynamicBytes.calldataSize (List.replicate length 0)) == [100, 132, 132, 164, 164])
    "last byte or calldata size changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := DynamicBytes.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.zip DynamicBytes.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    let seeded := DynamicBytes.seededPayloads (Seed.ofNat seed)
    ensure (seeded.length == 3 && seeded.all (·.length == 64)) "seeded payloads are not three 64-byte streams"
    match DynamicBytes.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 && Wire.programNodes value.program ≤ 384 &&
          value.plan.step.helpers.length == 1 + seed % 3) "bytes recipe lost node/transaction/helper bounds"
        ensure (value.transactions.map (·.payload.length) ==
            (choices.take 3).map fun choice => DynamicBytes.lengthBank.getD choice 0)
          "generated payload lengths escaped their draws"
        for (tx, index) in value.transactions.zipIdx do
          let length := tx.payload.length
          let expected := match choices.getD (3 + index) 0 with
            | 0 => List.replicate length 0
            | 1 => ones length
            | 2 => (List.range length).map fun position => (position + 1).toUInt8
            | _ => (seeded.getD index []).take length
          ensure (tx.payload == expected) "generated payload escaped its byte pattern"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == DynamicBytes.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (DynamicBytes.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (DynamicBytes.generatedScenario (Seed.ofNat 0) DynamicBytes.programOverhead) "undersized node budget accepted"
  let corpus := DynamicBytes.generateCases (Seed.ofNat 0) 384 4 512 10000
  ensure (corpus == DynamicBytes.generateCases (Seed.ofNat 0) 384 4 512 10000) "bytes generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "bytes count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (DynamicBytes.replayCase saved 10000)) == saved) "generated bytes provenance did not replay"
    let low ← get (DynamicBytes.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := DynamicBytes.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "bytes generation resource exhaustion was not distinguished"
  ensure ((← rows (DynamicBytes.generateCases (Seed.ofNat seed) 384 2 1 10000) "cases").size == 1 &&
    (← natural (DynamicBytes.generateCases (Seed.ofNat seed) 384 0 10 10000) "attempted") == 0 &&
    (← rows (DynamicBytes.generateCases (Seed.ofNat seed) 384 1 0 10000) "cases").isEmpty)
    "bytes generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("payload", toJson "0x0103"),
      ("payload", toJson "0x01030A"), ("payload", toJson "0X010307"),
      ("payload", toJson "010307"), ("payload", toJson "0x0103070"), ("payload", toJson ("0x" ++ String.join (List.replicate 65 "01"))),
      ("payload", toJson ([1, 3, 7] : List Nat)), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (DynamicBytes.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical bytes transaction accepted"
  -- Calldata that pads with nonzero bytes or names a different offset is not canonical.
  let calldata ← string first "calldata"
  rejected (DynamicBytes.decodeTransactions (toJson [first.setObjVal! "calldata" (toJson (String.ofList calldata.toList.dropLast.dropLast ++ "01"))]))
    "nonzero padding accepted"
  rejected (DynamicBytes.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "0000000000000040" "0000000000000060"))]))
    "noncanonical tail offset accepted"
  rejected (DynamicBytes.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (DynamicBytes.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (DynamicBytes.decodeTransactions (toJson (List.replicate 4 first))) "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson (["0", "1", "2", "3"] : List String)),
      ("observedSlots", toJson (["1", "0", "2", "3", "4"] : List String)),
      ("executionFuel", toJson (10000001 : Nat)), ("bytesPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (DynamicBytes.caseProgram (saved.setObjVal! name bad)) "invalid bytes case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (DynamicBytes.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 10000)
      "tampered bytes provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (DynamicBytes.replayCase (withOrigin (origin.setObjVal! name bad)) 10000)
      "tampered generated bytes recipe accepted"
  let generatedRows ← rows generated
  rejected (DynamicBytes.replayCase (generated.setObjVal! "transactions"
      (.arr (generatedRows.set! 0 (generatedRows[0]!.setObjVal! "payload" (toJson "0x"))))) 10000)
    "generated payload replaced without its seed"
  let plan ← field saved "bytesPlan"
  rejected (DynamicBytes.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical bytes plan accepted"
  rejected (DynamicBytes.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.dynamic-array-plan.v1")))
    "array plan schema accepted as a bytes plan"
  rejected (DynamicBytes.replayCase (saved.setObjVal! "source" (toJson "stale")) 10000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (DynamicBytes.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x9a94c44b"))) 10000)
    "array selector accepted for the bytes ABI"
  rejected (DynamicBytes.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-dynamic-array-case.v1")) 10000)
    "array case schema accepted by the bytes tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(1, ones 48), (0, (List.range 17).map (·.toUInt8)), (3, [0x80, 0x7f])]
  let saved ← imported value
  let candidates ← get (DynamicBytes.shrinkCases saved 2000 10000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (DynamicBytes.shrinkCases saved 2000 10000)))
    "bytes reductions were empty or nondeterministic"
  let mut removed := false
  let mut truncated := false
  let mut zeroed := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (DynamicBytes.caseProgram row)
    ensure (decide (DynamicBytes.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "bytes reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", DynamicBytes.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate bytes reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    truncated := truncated || (sameCount && pairs.any fun (left, right) =>
      left.payload.length < right.payload.length && left.payload == right.payload.take left.payload.length &&
        DynamicBytes.lengthBank.contains left.payload.length)
    zeroed := zeroed || (sameCount && pairs.any fun (left, right) =>
      left.payload.length == right.payload.length && left.payload != right.payload && left.payload.all (· == 0))
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (DynamicBytes.replayCase row 10000)) == row) "reduced bytes case did not replay"
  ensure (removed && truncated && zeroed && loweredFlags && changedStep)
    "bytes shrink omitted sequence/length/byte/flags/step axes"
  ensure ((← rows (← get (DynamicBytes.shrinkCases saved 2 10000)) "cases") == result.extract 0 2 &&
    (← rows (← get (DynamicBytes.shrinkCases saved 0 10000)) "cases").isEmpty) "bytes shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (DynamicBytes.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", DynamicBytes.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", DynamicBytes.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (DynamicBytes.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 10000)
    "non-strict bytes reduction provenance accepted"

def testSourceDynamicBytesCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceDynamicBytesCases
