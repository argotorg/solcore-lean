import Solcore.Synthesis.Source.MalformedNestedArrayCases

/-! Malformed-nested-array cases: generation is deterministic and validates
every prescribed std outcome against original Core; generated, imported and
reduced cases replay exactly; reductions remove transactions first and keep
the G0 revision and swarm mask; the emitted source is the nested-array emission
of the same step; and the case boundary rejects malformations outside their
bounds, row malformations of absent rows, more than four rows or three
elements, and any calldata or std outcome that differs from the malformation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedNestedArrayCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.MalformedNestedArrayExecution (Malformation Transaction)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) := get (corpus.getObjValAs? (Array Json) "cases")

private def w (value : Nat) : Word := Word.ofNatModulo value

def testSourceMalformedNestedArrayCases : IO Unit := do
  let corpus := MalformedNestedArray.generateCases (Seed.ofNat 1) 448 6 64 fuel .v3 8
  ensure (corpus == MalformedNestedArray.generateCases (Seed.ofNat 1) 448 6 64 fuel .v3 8) "generation is nondeterministic"
  ensure ((← get (corpus.getObjValAs? String "status")) == "complete") "generation did not complete"
  let generated ← cases corpus
  let mut kinds : List String := []
  let mut outcomes : List String := []
  for saved in generated do
    ensure ((← get (MalformedNestedArray.replayCase saved fuel)) == saved) "a generated case failed exact replay"
    let scenario ← get (MalformedNestedArray.caseProgram saved)
    ensure (scenario.transactions.length == 8) "a generated case lost its requested length"
    kinds := (kinds ++ scenario.transactions.map (MalformedNestedArray.kindOf ·.malformation)).eraseDups
    outcomes := (outcomes ++ scenario.transactions.map fun tx =>
      (MalformedNestedArray.prescribed tx).map MalformedNestedArray.selectorText |>.getD "accepted").eraseDups
    -- The compiled contract is the nested-array one.
    let emitted ← get (MalformedNestedArray.emit scenario.plan)
    let some nestedPlan := Solcore.Synthesis.Core.NestedArray.CheckedPlan.ofStep? scenario.plan.step
      | throw (IO.userError "the step failed nested-array admission")
    let nested ← get ((NestedArray.emit nestedPlan).mapError reprStr)
    ensure (emitted.source == nested.source) "the emitted source differs from the nested-array emission"
  ensure (MalformedNestedArray.malformationKinds.all kinds.contains) "generation misses a malformation kind"
  ensure (["0x4924aef0", "0x08638556", "accepted"].all outcomes.contains) "generation misses a std outcome"
  let some first := generated[0]? | throw (IO.userError "no generated case")
  let provenance ← get (first.getObjVal? "provenance")
  let reduced ← cases (← get (MalformedNestedArray.shrinkCases first 24 fuel))
  let some removal := reduced[0]? | throw (IO.userError "a generated case has no reduction")
  let original ← get (first.getObjValAs? (List Json) "transactions")
  ensure ((← get (removal.getObjValAs? (List Json) "transactions")) == original.dropLast)
    "the first reduction does not remove the last transaction"
  for candidate in reduced do
    ensure ((← get (MalformedNestedArray.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let candidateProvenance ← get (candidate.getObjVal? "provenance")
    ensure ((candidateProvenance.getObjVal? "swarmMask").toOption == (provenance.getObjVal? "swarmMask").toOption &&
      (candidateProvenance.getObjVal? "generatorVersion").toOption == (provenance.getObjVal? "generatorVersion").toOption)
      "a reduction lost the parent's revision or swarm mask"
  -- An imported sequence through the case boundary: a malformed unread fourth
  -- row is accepted and a malformed read row is rejected.
  let scenario ← get (MalformedNestedArray.caseProgram first)
  let base : Transaction := ⟨"tx-0", w 2, [[w 3], [], [w 7, w 1, w 0], [w 1]], .none⟩
  let imported ← get (MalformedNestedArray.checkedScenario scenario.plan
    [base, {base with id := "tx-1", malformation := .rowLength 3 (w (2 ^ 256 - 1))},
      {base with id := "tx-2", malformation := .rowOffset 1 (w (2 ^ 256 - 32))}])
  let importedCase ← get (MalformedNestedArray.emitCase imported (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← get (MalformedNestedArray.replayCase importedCase fuel)) == importedCase) "an imported case failed exact replay"
  let rows ← get (importedCase.getObjValAs? (Array Json) "transactions")
  ensure ((rows.map fun row => (row.getObjVal? "stdRejection").toOption) ==
      #[some Json.null, some Json.null, some (toJson "0x08638556")]) "an imported case records other std outcomes"
  -- Malformations outside their bounds, row malformations of absent rows, too
  -- many rows, elements or transactions, and tampered calldata or std outcomes
  -- are rejected.
  for malformation in [Malformation.short 4, .selector 0, .selector (2 ^ 32), .truncate 3, .truncate 516,
      .trailing 0 0, .trailing 65 0, .trailing 1 3, .rowOffset 4 Word.zero, .rowLength 4 Word.zero] do
    rejected (MalformedNestedArray.checkedScenario scenario.plan [{base with malformation}])
      "a malformation outside its bounds was admitted"
  rejected (MalformedNestedArray.checkedScenario scenario.plan [{base with values := base.values ++ [[]]}])
    "five rows were admitted"
  rejected (MalformedNestedArray.checkedScenario scenario.plan [{base with values := [[w 1, w 2, w 3, w 4]]}])
    "four elements were admitted"
  rejected (MalformedNestedArray.checkedScenario scenario.plan
    ((List.range (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1)).map fun index =>
      {base with id := "tx-" ++ toString index}))
    "an unbounded sequence was admitted"
  let row := rows[2]!
  for (key, value) in [("calldata", toJson "0x7095aff8"), ("stdRejection", Json.null),
      ("stdRejection", toJson "0x4924aef0"), ("value", toJson "1")] do
    rejected (MalformedNestedArray.decodeTransactions (toJson [row.setObjVal! key value]))
      s!"a transaction with a changed {key} was admitted"

end Tests.SourceMalformedNestedArrayCases
