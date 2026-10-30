import Solcore.Synthesis.Source.LongBytesCases

/-! Long-bytes case regressions: exact replay, bounded generation from an
independent sequence stream, canonical payload and calldata boundaries up to
256 bytes, and typed reductions over steps, transactions, payload lengths,
payload bytes and flags. Expected values here are test goldens only; cases and
the observer never consume them. -/
set_option autoImplicit false

namespace Tests.SourceLongBytesCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Core.LongBytes (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicBytesExecution (Transaction)
open Solcore.Synthesis.Stateful.LongBytesExecution (Bindings)

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
private def ramp (length : Nat) : List UInt8 := (List.range length).map fun index => (index + 1).toUInt8

private def makePlan (body : Wire.Expr) (result : Wire.Expr := entry) : IO CheckedPlan := do
  let some graph := Aggregates.CheckedDAG.ofParts? [body] result |
    throw (IO.userError "long-bytes fixture failed step admission")
  let some plan := CheckedPlan.ofStep? graph | throw (IO.userError "long-bytes wrapper failed host admission")
  return plan
private def transactions (values : List (Nat × List UInt8)) : List Transaction :=
  values.zipIdx.map fun ((flags, payload), index) => ⟨"call-" ++ toString index, Word.ofNatModulo flags, payload⟩
private def scenario (plan : CheckedPlan) (values : List (Nat × List UInt8)) : IO LongBytes.CheckedScenario :=
  get (LongBytes.checkedScenario plan (transactions values))
private def imported (value : LongBytes.CheckedScenario) (fuel : Nat := 1000000) : IO Json :=
  get (LongBytes.emitCase value (Json.mkObj [("kind", toJson "imported")]) fuel)

private def referenceChecks : IO Json := do
  let identity ← makePlan (.var 0)
  let value ← scenario identity [(0, ramp 97), (1, ones 256), (2, [])]
  let saved ← imported value
  ensure ((← field saved "observedSlots") == toJson ((List.range 11).map toString))
    "case did not declare slots zero through ten"
  ensure ((← get (LongBytes.replayCase saved 1000000)) == saved) "imported long-bytes case did not replay"
  ensure ((← get (LongBytes.replayCase (saved.setObjVal! "directCore" (toJson "forged")) 1000000)) == saved)
    "long-bytes replay consumed a stored expected result"
  let changed ← imported (← scenario identity [(5, []), (2, [9, 9])])
  ensure ((← field saved "program") == (← field changed "program") &&
    (← string saved "source") == (← string changed "source"))
    "payloads or flags were substituted into source or Core code"
  ensure (((← rows saved).map fun row => (row.getObjValAs? String "payload").toOption) ==
      #[some ("0x" ++ String.join ((List.range 97).map fun index =>
          let digits := Nat.toDigits 16 (index + 1)
          String.ofList (List.replicate (2 - digits.length) '0' ++ digits))),
        some ("0x" ++ String.join (List.replicate 256 "ff")), some "0x"])
    "payloads are not canonical lowercase hexadecimal"
  let observed := LongBytes.observe value bindings 1000000
  ensure ((← string observed "status") == "complete" &&
    ((← rows observed).map fun row => (row.getObjValAs? String "status").toOption) ==
      #[some "returned", some "reverted", some "returned"])
    "long-bytes scenario did not follow its flags parities"
  ensure ((← get (LongBytes.checkProtocol value observed)) == ["returned", "reverted", "returned"])
    "long-bytes history broke its length, last-byte or sum protocol"
  let rebound ← rows (LongBytes.observe value ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000)
  ensure (rebound.map Solcore.Synthesis.Stateful.AccountStorage.unbound == (← rows observed).map Solcore.Synthesis.Stateful.AccountStorage.unbound &&
      rebound.all (Solcore.Synthesis.Stateful.AccountStorage.boundTo · [202]))
    "address-independent long-bytes profile changed with bindings"
  rejected (LongBytes.checkedScenario identity (transactions [(0, List.replicate 257 1)])) "257-byte payload accepted"
  ensure (LongBytes.tailByte [] == 0 && LongBytes.tailByte [1, 2, 0x80] == 0x80 &&
    [0, 1, 64, 65, 97, 255, 256].map (fun length => LongBytes.calldataSize (List.replicate length 0)) ==
      [100, 132, 164, 196, 228, 356, 356])
    "last byte or calldata size changed"
  return saved

private def generationChecks : IO Json := do
  for seed in List.range 8 do
    let choices := LongBytes.sequenceChoices (Seed.ofNat seed)
    ensure (choices.length == 7 && (choices.zip LongBytes.sequenceBounds).all (fun (value, bound) => value < bound))
      "sequence choices escaped their banks"
    let seeded := LongBytes.seededPayloads (Seed.ofNat seed)
    ensure (seeded.length == 3 && seeded.all (·.length == 256)) "seeded payloads are not three 256-byte streams"
    match LongBytes.generatedScenario (Seed.ofNat seed) 384 with
    | .error _ => pure ()
    | .ok (value, origin) =>
        ensure (value.transactions.length == 3 &&
          Wire.programNodes value.program ≤ 384 + Solcore.Synthesis.Core.LongBytes.guardNodes &&
          value.plan.step.helpers.length == 1 + seed % 3) "long-bytes recipe lost node/transaction/helper bounds"
        ensure (value.transactions.map (·.payload.length) ==
            (choices.take 3).map fun choice => LongBytes.lengthBank.getD choice 0)
          "generated payload lengths escaped their draws"
        for (tx, index) in value.transactions.zipIdx do
          let length := tx.payload.length
          let expected := match choices.getD (3 + index) 0 with
            | 0 => List.replicate length 0
            | 1 => ones length
            | 2 => (List.range length).map fun position => (position + 1).toUInt8
            | _ => (seeded.getD index []).take length
          ensure (tx.payload == expected) "generated payload escaped its byte pattern"
        ensure ((value.transactions.map fun tx => tx.flags.val % 2 == 1) == LongBytes.generatedParities (Seed.ofNat seed) &&
          value.transactions.all (fun tx => tx.flags.val < 2))
          "generated flags are not exactly their prescribed parities"
        ensure ((origin.getObjValAs? (List Nat) "sequenceChoices").toOption == some choices)
          "generated origin lost its sequence choices"
  rejected (LongBytes.generatedScenario (Seed.ofNat 0) 513) "oversized node budget accepted"
  rejected (LongBytes.generatedScenario (Seed.ofNat 0) Solcore.Synthesis.Core.LongBytes.programOverhead)
    "undersized node budget accepted"
  let corpus := LongBytes.generateCases (Seed.ofNat 0) 384 4 512 1000000
  ensure (corpus == LongBytes.generateCases (Seed.ofNat 0) 384 4 512 1000000) "long-bytes generation nondeterministic"
  let generated ← rows corpus "cases"
  ensure (generated.size == 4 && (← natural corpus "attempted") ≤ 512 && (← string corpus "status") == "complete")
    "long-bytes count does not count complete scenarios"
  for saved in generated do
    ensure ((← get (LongBytes.replayCase saved 1000000)) == saved) "generated long-bytes provenance did not replay"
    let low ← get (LongBytes.replayCase saved 0)
    ensure ((← natural low "executionFuel") == 0 && (← field low "provenance") == (← field saved "provenance"))
      "fresh replay fuel changed the generation validation budget"
  let saved := generated[0]!
  let origin ← field (← field saved "provenance") "origin"
  let some seed := (← string origin "seed").toNat? | throw (IO.userError "invalid generated seed")
  let low := LongBytes.generateCases (Seed.ofNat seed) 384 1 1 0
  let excluded ← rows low "excluded"
  ensure ((← rows low "cases").isEmpty && (← string excluded[0]! "category") == "inconclusive-resource")
    "long-bytes generation resource exhaustion was not distinguished"
  ensure ((← rows (LongBytes.generateCases (Seed.ofNat seed) 384 2 1 1000000) "cases").size == 1 &&
    (← natural (LongBytes.generateCases (Seed.ofNat seed) 384 0 10 1000000) "attempted") == 0 &&
    (← rows (LongBytes.generateCases (Seed.ofNat seed) 384 1 0 1000000) "cases").isEmpty)
    "long-bytes generator ignored count/attempt bounds"
  return saved

private def tamperingChecks (saved generated : Json) : IO Unit := do
  let first := (← rows saved)[0]!
  for (name, bad) in [("id", toJson ""), ("id", toJson "not valid"), ("flags", toJson "01"),
      ("flags", toJson (toString (2 ^ 256))), ("flags", toJson "2"), ("payload", toJson "0x0103"),
      ("payload", toJson "0x01030A"), ("payload", toJson "0X010307"),
      ("payload", toJson "010307"), ("payload", toJson "0x0103070"), ("payload", toJson ("0x" ++ String.join (List.replicate 257 "01"))),
      ("payload", toJson ([1, 3, 7] : List Nat)), ("calldata", toJson "0x"), ("value", toJson "1"), ("extra", toJson true)] do
    rejected (LongBytes.decodeTransactions (toJson [first.setObjVal! name bad]))
      "noncanonical long-bytes transaction accepted"
  -- Calldata that pads with nonzero bytes or names a different offset is not canonical.
  let calldata ← string first "calldata"
  rejected (LongBytes.decodeTransactions (toJson [first.setObjVal! "calldata" (toJson (String.ofList calldata.toList.dropLast.dropLast ++ "01"))]))
    "nonzero padding accepted"
  rejected (LongBytes.decodeTransactions (toJson [first.setObjVal! "calldata"
      (toJson (calldata.replace "0000000000000040" "0000000000000060"))]))
    "noncanonical tail offset accepted"
  rejected (LongBytes.decodeTransactions (toJson [first, first])) "duplicate transaction IDs accepted"
  rejected (LongBytes.decodeTransactions (toJson ([] : List Json))) "empty transaction list accepted"
  rejected (LongBytes.decodeTransactions
    (toJson (List.replicate (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1) first)))
    "unbounded transaction count accepted"
  for (name, bad) in [("initialState", Json.mkObj [("storage", toJson [first])]),
      ("observedSlots", toJson ((List.range 10).map toString)),
      ("observedSlots", toJson (["0", "1", "2", "3", "4"] : List String)),
      ("observedSlots", toJson (["1", "0"] ++ (List.range 9).map (toString ∘ (· + 2)))),
      ("executionFuel", toJson (10000001 : Nat)), ("longBytesPlan", Json.null),
      ("program", Wire.encodeProgram {resultType := .word, dataDefinitions := [], body := word 0})] do
    rejected (LongBytes.caseProgram (saved.setObjVal! name bad)) "invalid long-bytes case boundary accepted"
  let provenance ← field generated "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun changed => generated.setObjVal! "provenance" (provenance.setObjVal! "origin" changed)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "templateVersion", "stepProfileVersion",
      "stepFunctionVersion", "stepTemplateVersion", "emitterVersion", "wrapperVersion", "features"] do
    rejected (LongBytes.replayCase (generated.setObjVal! "provenance" (provenance.setObjVal! name Json.null)) 1000000)
      "tampered long-bytes provenance accepted"
  for (name, bad) in [("seed", toJson "00"), ("finalSeed", toJson "bad"),
      ("maxProgramNodes", toJson (513 : Nat)), ("stepOrigin", Json.null), ("sequenceChoices", Json.null),
      ("sequenceCompletions", Json.null), ("validationFuel", toJson (10000001 : Nat)), ("validationFuel", toJson (0 : Nat))] do
    rejected (LongBytes.replayCase (withOrigin (origin.setObjVal! name bad)) 1000000)
      "tampered generated long-bytes recipe accepted"
  let generatedRows ← rows generated
  -- Any other payload than the seed's: the empty one, or one byte when the seed's is empty.
  let generatedPayload := (generatedRows[0]!.getObjValAs? String "payload").toOption.getD ""
  rejected (LongBytes.replayCase (generated.setObjVal! "transactions"
      (.arr (generatedRows.set! 0 (generatedRows[0]!.setObjVal! "payload"
        (toJson (if generatedPayload == "0x" then "0x00" else "0x")))))) 1000000)
    "generated payload replaced without its seed"
  let plan ← field saved "longBytesPlan"
  rejected (LongBytes.checkedPlan (plan.setObjVal! "extra" Json.null)) "noncanonical long-bytes plan accepted"
  rejected (LongBytes.checkedPlan (plan.setObjVal! "schema" (toJson "solcore-lean.bytes-plan.v1")))
    "the 64-byte profile's plan schema accepted as a long-bytes plan"
  rejected (LongBytes.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000000) "stale source accepted"
  let contract ← field saved "contract"
  rejected (LongBytes.replayCase (saved.setObjVal! "contract" (contract.setObjVal! "selector" (toJson "0x9a94c44b"))) 1000000)
    "array selector accepted for the long-bytes ABI"
  rejected (LongBytes.replayCase (saved.setObjVal! "schema" (toJson "solcore-lean.semantic-bytes-case.v1")) 1000000)
    "the 64-byte profile's case schema accepted by the long-bytes tool"

private def shrinkChecks : IO Unit := do
  let plan ← makePlan (Aggregate.template 3 (word 2))
  let value ← scenario plan [(1, ones 200), (0, (List.range 129).map (·.toUInt8)), (3, [0x80, 0x7f])]
  let saved ← imported value
  let candidates ← get (LongBytes.shrinkCases saved 2000 1000000)
  let result ← rows candidates "cases"
  ensure (!result.isEmpty && candidates == (← get (LongBytes.shrinkCases saved 2000 1000000)))
    "long-bytes reductions were empty or nondeterministic"
  let mut removed := false
  let mut truncated := false
  let mut zeroed := false
  let mut loweredFlags := false
  let mut changedStep := false
  let mut seen : List String := []
  for row in result do
    let reduced ← get (LongBytes.caseProgram row)
    ensure (decide (LongBytes.StrictlySmaller reduced value) && reduced.program.check &&
      reduced.plan.step.helpers.length == value.plan.step.helpers.length &&
      Aggregate.bindingInventory reduced.plan.step == Aggregate.bindingInventory value.plan.step &&
      decide ((reduced.transactions.map (·.id)).Sublist (value.transactions.map (·.id))))
      "long-bytes reduction lost strict complexity, host typing or stable scope/IDs"
    let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.program),
      ("transactions", LongBytes.transactionsJson reduced.transactions)]).compress
    ensure (!seen.contains identity) "duplicate long-bytes reduction"
    seen := identity :: seen
    removed := removed || reduced.transactions.length < value.transactions.length
    let pairs := reduced.transactions.zip value.transactions
    let sameCount := reduced.transactions.length == value.transactions.length
    truncated := truncated || (sameCount && pairs.any fun (left, right) =>
      left.payload.length < right.payload.length && left.payload == right.payload.take left.payload.length &&
        LongBytes.lengthBank.contains left.payload.length)
    zeroed := zeroed || (sameCount && pairs.any fun (left, right) =>
      left.payload.length == right.payload.length && left.payload != right.payload && left.payload.all (· == 0))
    loweredFlags := loweredFlags || (sameCount && pairs.any fun (left, right) => left.flags.val < right.flags.val)
    changedStep := changedStep || Wire.encodeProgram reduced.program != Wire.encodeProgram value.program
    ensure ((← get (LongBytes.replayCase row 1000000)) == row) "reduced long-bytes case did not replay"
  ensure (removed && truncated && zeroed && loweredFlags && changedStep)
    "long-bytes shrink omitted sequence/length/byte/flags/step axes"
  ensure ((← rows (← get (LongBytes.shrinkCases saved 2 1000000)) "cases") == result.extract 0 2 &&
    (← rows (← get (LongBytes.shrinkCases saved 0 1000000)) "cases").isEmpty) "long-bytes shrink limit changed ordering"
  let first := result[0]!
  let reduced ← get (LongBytes.caseProgram first)
  let badParent := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", LongBytes.planJson reduced.plan),
    ("parentProgram", Wire.encodeProgram reduced.program),
    ("parentTransactions", LongBytes.transactionsJson reduced.transactions)]
  let provenance ← field first "provenance"
  rejected (LongBytes.replayCase (first.setObjVal! "provenance" (provenance.setObjVal! "origin" badParent)) 1000000)
    "non-strict long-bytes reduction provenance accepted"

def testSourceLongBytesCases : IO Unit := do
  let imported ← referenceChecks
  let generated ← generationChecks
  tamperingChecks imported generated
  shrinkChecks

end Tests.SourceLongBytesCases
