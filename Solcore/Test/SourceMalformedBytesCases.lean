import Solcore.Synthesis.Source.MalformedBytesCases

/-! Malformed-bytes cases: generation is deterministic and validates every
prescribed std outcome against original Core; generated, imported and reduced
cases replay exactly; reductions remove transactions first and keep the G0
revision and swarm mask; the emitted source is the long-bytes emission of the
same step; and the case boundary rejects malformations outside their bounds,
padding malformations without padding, payloads over 256 bytes, and any
calldata or std outcome that differs from the malformation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedBytesCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.MalformedBytesExecution (Malformation Transaction)

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

private def ramp (count : Nat) : List UInt8 := (List.range count).map fun position => (position + 1).toUInt8

def testSourceMalformedBytesCases : IO Unit := do
  let corpus := MalformedBytes.generateCases (Seed.ofNat 1) 448 6 64 fuel .v3 8
  ensure (corpus == MalformedBytes.generateCases (Seed.ofNat 1) 448 6 64 fuel .v3 8) "generation is nondeterministic"
  ensure ((← get (corpus.getObjValAs? String "status")) == "complete") "generation did not complete"
  let generated ← cases corpus
  let mut kinds : List String := []
  let mut outcomes : List String := []
  for saved in generated do
    ensure ((← get (MalformedBytes.replayCase saved fuel)) == saved) "a generated case failed exact replay"
    let scenario ← get (MalformedBytes.caseProgram saved)
    ensure (scenario.transactions.length == 8) "a generated case lost its requested length"
    kinds := (kinds ++ scenario.transactions.map (MalformedBytes.kindOf ·.malformation)).eraseDups
    outcomes := (outcomes ++ scenario.transactions.map fun tx =>
      (MalformedBytes.prescribed tx).map MalformedBytes.selectorText |>.getD "accepted").eraseDups
    -- The compiled contract is the long-bytes one.
    let emitted ← get (MalformedBytes.emit scenario.plan)
    let some bytesPlan := Solcore.Synthesis.Core.LongBytes.CheckedPlan.ofStep? scenario.plan.step
      | throw (IO.userError "the step failed long-bytes admission")
    let long ← get ((LongBytes.emit bytesPlan).mapError reprStr)
    ensure (emitted.source == long.source) "the emitted source differs from the long-bytes emission"
  ensure (MalformedBytes.malformationKinds.all kinds.contains) "generation misses a malformation kind"
  ensure (["0x4924aef0", "0x08638556", "accepted"].all outcomes.contains) "generation misses a std outcome"
  let some first := generated[0]? | throw (IO.userError "no generated case")
  let provenance ← get (first.getObjVal? "provenance")
  let reduced ← cases (← get (MalformedBytes.shrinkCases first 24 fuel))
  let some removal := reduced[0]? | throw (IO.userError "a generated case has no reduction")
  let original ← get (first.getObjValAs? (List Json) "transactions")
  ensure ((← get (removal.getObjValAs? (List Json) "transactions")) == original.dropLast)
    "the first reduction does not remove the last transaction"
  for candidate in reduced do
    ensure ((← get (MalformedBytes.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let candidateProvenance ← get (candidate.getObjVal? "provenance")
    ensure ((candidateProvenance.getObjVal? "swarmMask").toOption == (provenance.getObjVal? "swarmMask").toOption &&
      (candidateProvenance.getObjVal? "generatorVersion").toOption == (provenance.getObjVal? "generatorVersion").toOption)
      "a reduction lost the parent's revision or swarm mask"
  -- An imported sequence through the case boundary: a cut inside the padding
  -- and nonzero padding are accepted, a cut inside the payload is rejected.
  let scenario ← get (MalformedBytes.caseProgram first)
  let base : Transaction := ⟨"tx-0", w 2, ramp 65, .none⟩
  let imported ← get (MalformedBytes.checkedScenario scenario.plan
    [{base with malformation := .truncate 180}, {base with id := "tx-1", malformation := .padding 1},
      {base with id := "tx-2", malformation := .truncate 164}])
  let importedCase ← get (MalformedBytes.emitCase imported (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← get (MalformedBytes.replayCase importedCase fuel)) == importedCase) "an imported case failed exact replay"
  let rows ← get (importedCase.getObjValAs? (Array Json) "transactions")
  ensure ((rows.map fun row => (row.getObjVal? "stdRejection").toOption) ==
      #[some Json.null, some Json.null, some (toJson "0x08638556")]) "an imported case records other std outcomes"
  -- Malformations outside their bounds, padding without padding, an unknown
  -- padding pattern, payloads over 256 bytes, too many transactions, and
  -- tampered calldata or std outcomes are rejected.
  for malformation in [Malformation.short 4, .selector 0, .selector (2 ^ 32), .truncate 3, .truncate 196,
      .trailing 0 0, .trailing 65 0, .trailing 1 3, .padding 3] do
    rejected (MalformedBytes.checkedScenario scenario.plan [{base with malformation}])
      "a malformation outside its bounds was admitted"
  rejected (MalformedBytes.checkedScenario scenario.plan [{base with payload := ramp 64, malformation := .padding 0}])
    "padding without padding bytes was admitted"
  rejected (MalformedBytes.checkedScenario scenario.plan [{base with payload := ramp 257}])
    "a 257-byte payload was admitted"
  rejected (MalformedBytes.checkedScenario scenario.plan
    ((List.range (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1)).map fun index =>
      {base with id := "tx-" ++ toString index}))
    "an unbounded sequence was admitted"
  let row := rows[2]!
  for (key, value) in [("calldata", toJson "0x220eb9b6"), ("stdRejection", Json.null),
      ("stdRejection", toJson "0x4924aef0"), ("value", toJson "1")] do
    rejected (MalformedBytes.decodeTransactions (toJson [row.setObjVal! key value]))
      s!"a transaction with a changed {key} was admitted"

end Tests.SourceMalformedBytesCases
