import Solcore.Synthesis.Source.MalformedBytesCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Core.LongBytes
import Solcore.Synthesis.Stateful.MalformedBytesExecution
import Solcore.Synthesis.Source.MalformedCalldataCases
import Solcore.Synthesis.Core.DynamicArray
import Solcore.Synthesis.Stateful.MalformedCalldataExecution
import Solcore.Synthesis.Source.MalformedNestedArrayCases
import Solcore.Synthesis.Core.NestedArray
import Solcore.Synthesis.Stateful.MalformedNestedArrayExecution

/-!
# Malformed calldata profile tests

Malformed calldata, bytes and nested arrays, against the std model.
-/

section
-- leanmerge: from Solcore.Test.SourceMalformedBytesCases
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
end

section
-- leanmerge: from Solcore.Test.SourceMalformedBytesCorpus
/-! The fixed malformed-bytes corpus checks actual original Core histories
against expectations computed without the std-modeling wrapper: a prescribed
std rejection reverts with its selector Word and keeps the slots; an accepted
transaction is the canonical long-bytes contract on the payload std decodes,
its result moved by the calldata size. Coverage describes the checked step
AST, the canonical payload lengths and chunk Words, the malformation kinds,
the prescribed std outcomes and the completions. Source/Rust/EVM agreement is a
separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedBytesCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", MalformedBytes.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.MalformedBytes.version),
  ("templateVersion", MalformedBytes.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", MalformedBytes.emitterVersion), ("wrapperVersion", MalformedBytes.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The zero-padded 32-byte chunk Words of a payload, which the step folds. -/
private def chunks (payload : List UInt8) : List String :=
  (List.range ((payload.length + 31) / 32)).map fun index =>
    let chunk : List UInt8 := ((payload.drop (32 * index)).take 32 ++ List.replicate 32 0).take 32
    toString (chunk.foldl (fun total byte => total * 256 + byte.toNat) 0)

/-- The prescribed std outcomes, by name. -/
private def outcomeNames : List String :=
  ["0x4924aef0", "0x08638556", "accepted"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := MalformedBytes.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← MalformedBytes.checkedPlan (← entry.getObjVal? "malformedBytesPlan")
  let scenario ← MalformedBytes.checkedScenario plan
    (← MalformedBytes.decodeTransactions (← entry.getObjVal? "transactions"))
  MalformedBytes.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "malformed-bytes-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-malformed-bytes" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected malformed-bytes manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("malformed-bytes manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words Storage.boundaryInputs))
    "malformed-bytes corpus must require all six boundary Words as chunks"
  require ((← manifest.getObjValAs? (List Nat) "requiredPayloadLengths") == MalformedBytes.lengthBank)
    "malformed-bytes corpus must require every bank payload length"
  require ((← strings manifest "requiredMalformations") == MalformedBytes.malformationKinds)
    "malformed-bytes corpus must require every malformation kind"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "malformed-bytes corpus must require both std rejections and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "malformed-bytes corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "malformed-bytes corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "malformed-bytes corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "malformed-bytes corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "malformed-bytes corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut lengths : List Nat := []
  let mut kinds : List String := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate malformed-bytes corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← MalformedBytes.replayCase saved fuel) == saved) ("malformed-bytes corpus entry did not replay: " ++ identifier)
    let scenario ← MalformedBytes.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "malformedBytesPlan") == (← entry.getObjVal? "malformedBytesPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported malformed-bytes entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("malformed-bytes corpus features changed: " ++ identifier)
    let history := MalformedBytes.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("malformed-bytes corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("malformed-bytes expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => chunks tx.payload).eraseDups
    lengths := (lengths ++ scenario.transactions.map (·.payload.length)).eraseDups
    kinds := (kinds ++ scenario.transactions.map (MalformedBytes.kindOf ·.malformation)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (MalformedBytes.prescribed tx).map MalformedBytes.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "malformed-bytes corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "malformed-bytes corpus misses a boundary chunk Word"
  require (MalformedBytes.lengthBank.all lengths.contains) "malformed-bytes corpus misses a payload length"
  require (MalformedBytes.malformationKinds.all kinds.contains) "malformed-bytes corpus misses a malformation kind"
  require (outcomeNames.all rejections.contains) "malformed-bytes corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "malformed-bytes corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "malformed-bytes corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "malformed-bytes corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-malformed-bytes"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("malformations", toJson kinds), ("rejections", toJson rejections),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid malformed-bytes corpus unexpectedly passed")

def testSourceMalformedBytesCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-malformed-bytes-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first malformed-bytes case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated malformed-bytes case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- A std rejection's selector, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "none")])))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-long-bytes"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredPayloadLengths", toJson [0, 1, 64]),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredMalformations", toJson (["none"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMalformedBytesCorpus
end

section
-- leanmerge: from Solcore.Test.SourceMalformedBytesGolden
/-! Golden cases for the std model behind the malformed-bytes profile. The
expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol` (`decodeBytesLike`), not computed by either model:
a rejection reverts with its error selector as a Word and keeps the empty
storage; an accepted malformation behaves exactly like the canonical
long-bytes contract on the payload std decodes, except that its result counts
the actual calldata size. Both the Core wrapper and the byte-level
`stdDecode` must give that outcome. Cases with two defects check std's decode
order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedBytesGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedBytesExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags and payload. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags : Nat) (payload : List Nat)

private def noSelector : Expected := .rejected StdDispatch.noSelectorError
private def truncated : Expected := .rejected StdDispatch.truncatedError

/-- The ramp `1, 2, ..., count`. -/
private def ramp (count : Nat) : List Nat := (List.range count).map (· + 1)

/-- 65 bytes, flags 2 (even, so the body returns): the payload at bytes 100 to
164 and 31 bytes of zero padding to 196. -/
private def odd : List Nat := ramp 65
/-- 64 bytes without padding; 164 bytes of calldata. -/
private def even : List Nat := ramp 64

private def malformed (payload : List Nat) (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w 2, payload.map Nat.toUInt8, malformation⟩

private def cases : List (String × List Nat × Malformation × Expected) := [
  ("canonical", odd, .none, .accepted 2 odd),
  ("short-0", odd, .short 0, noSelector), ("short-3", odd, .short 3, noSelector),
  ("wrong-selector-low", odd, .selector 1, noSelector),
  ("wrong-selector-high", odd, .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", odd, .selector (2 ^ 32 - 1), noSelector),
  ("truncated-selector-only", odd, .truncate 4, truncated),
  ("truncated-head", odd, .truncate 67, truncated),
  -- 31 bytes remain at 4 + 64.
  ("truncated-length", odd, .truncate 99, truncated),
  -- The last payload byte at 164 is cut.
  ("truncated-payload", odd, .truncate 164, truncated),
  -- Only padding is cut: std neither requires nor reads it.
  ("cut-all-padding", odd, .truncate 165, .accepted 2 odd),
  ("cut-last-padding-byte", odd, .truncate 195, .accepted 2 odd),
  ("truncated-unpadded-payload", even, .truncate 163, truncated),
  ("trailing-1-zero", odd, .trailing 1 0, .accepted 2 odd),
  ("trailing-33-ones", odd, .trailing 33 1, .accepted 2 odd),
  ("trailing-64-ramp", odd, .trailing 64 2, .accepted 2 odd),
  ("offset-past-end", odd, .offset (w 193), truncated),
  ("offset-partial-length", odd, .offset (w 161), truncated),
  ("offset-high-bit", odd, .offset (w (2 ^ 255)), truncated),
  ("offset-wraps", odd, .offset (w (2 ^ 256 - 4)), truncated),
  -- Offset 0: the length is the flags Word, 2, and the payload the first two
  -- bytes of the offset Word, now zero.
  ("offset-overlaps-flags", odd, .offset (w 0), .accepted 2 [0, 0]),
  -- Offset 32: the length is the offset Word, 32, and the payload is the
  -- original length Word, which ends in 65.
  ("offset-overlaps-itself", odd, .offset (w 32), .accepted 2 (List.replicate 31 0 ++ [65])),
  -- One byte of the padding becomes payload.
  ("length-into-padding", odd, .length (w 66), .accepted 2 (odd ++ [0])),
  ("length-most-that-fits", odd, .length (w 96), .accepted 2 (odd ++ List.replicate 31 0)),
  ("length-past-data", odd, .length (w 97), truncated),
  ("length-past-unpadded-data", even, .length (w 65), truncated),
  -- Above ~0 - 63: the range check rejects before std's bound.
  ("length-above-bound", odd, .length (w (2 ^ 256 - 63)), truncated),
  ("length-maximum", odd, .length (w (2 ^ 256 - 1)), truncated),
  ("length-high-bit", odd, .length (w (2 ^ 255)), truncated),
  ("length-one-shorter", odd, .length (w 64), .accepted 2 even),
  ("length-zero", odd, .length (w 0), .accepted 2 []),
  -- Nonzero padding is ignored.
  ("padding-ones", odd, .padding 0, .accepted 2 odd),
  ("padding-ramp", odd, .padding 1, .accepted 2 odd),
  ("padding-last-byte", odd, .padding 2, .accepted 2 odd)]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def canonical (payload : List Nat) : ByteArray :=
  DynamicBytesExecution.inputBytes (w 2) (payload.map Nat.toUInt8)

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a bad length: dispatch fails first.
  ("wrong-selector-and-bad-length",
    StdCalldata.replaceWord ((StdCalldata.Change.selector 1).apply (canonical odd)) 68 (w (2 ^ 256 - 1)), noSelector),
  ("three-selector-bytes", bytes ((selectorBytes MalformedBytes.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedBytes.selector ++ wordBytes 2 ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping offset and a bad length: the offset is checked first.
  ("bad-offset-and-length",
    StdCalldata.replaceWord (StdCalldata.replaceWord (canonical odd) 36 (w (2 ^ 256 - 4))) 68 (w (2 ^ 256 - 1)), truncated),
  -- Nonzero padding with a cut inside it: the last payload Word at 164 keeps
  -- its payload byte 65 and gains `0xff` padding, cut after 180 bytes.
  ("ones-padding-then-cut", ((StdCalldata.Change.word 164 (w (2 ^ 248 * 65 + (2 ^ 248 - 1)))).apply (canonical odd)).extract 0 180,
    .accepted 2 odd),
  -- The dynamic-array selector with a canonical bytes body is no match.
  ("dynamic-array-selector-bytes-body",
    bytes (selectorBytes 0x9a94c44b) ++ (canonical odd).extract 4 (canonical odd).size, noSelector)]

private def selectorOutput (selector : Nat) : String := encodeBytesText (encodeWordBytesBE (w selector))

private def row (history : Json) : IO Json := do
  let some first := (← get (history.getObjValAs? (Array Json) "transactions"))[0]?
    | throw (IO.userError "no transaction row")
  return first

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        let storage := match terminal.finalWorld.account? bindings.address with
          | some account => LongBytesExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage),
          ("accountStorage", AccountStorage.contractJson terminal.finalWorld bindings.address)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

/-- The Word a row returns or reverts with. -/
private def outputWord (row : Json) : IO Nat := do
  let some bytes := decodeBytesText? (← get (row.getObjValAs? String "output"))
    | throw (IO.userError "output is not hexadecimal")
  return StdCalldata.wordAt bytes 0

private def checkExpected (name : String) (canonicalPlan : LongBytes.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
      let empty := LongBytesExecution.observe canonicalPlan [] StorageExecution.fixtureBindings fuel
      ensure ((outcome.getObjVal? "committedStorage").toOption == (empty.getObjVal? "initialStorage").toOption &&
        (outcome.getObjVal? "accountStorage").toOption == (empty.getObjVal? "initialAccountStorage").toOption)
        s!"{name}: a std rejection changed storage"
  | .accepted flags payload =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedBytesExecution.stdDecoded? input == some (flags, payload.map Nat.toUInt8))
        s!"{name}: the byte model decodes another payload"
      -- The canonical long-bytes contract on the decoded payload is the
      -- reference for the body; its result counts the canonical calldata size.
      let bytesPayload := payload.map Nat.toUInt8
      let reference := LongBytesExecution.observe canonicalPlan [⟨"tx-0", w flags, bytesPayload⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      for key in ["status", "committedStorage", "accountStorage"] do
        ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
          s!"{name}: {key} differs from the canonical contract on the decoded payload"
      let canonicalSize := (DynamicBytesExecution.inputBytes (w flags) bytesPayload).size
      ensure ((← outputWord outcome) == ((← outputWord referenceRow) + input.size - canonicalSize) % 2 ^ 256)
        s!"{name}: the result differs from the canonical contract's beyond the calldata size"

def testSourceMalformedBytesGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedBytes.selector == 0x220eb9b6) "the profile selector is not run(uint256,bytes)"
  ensure ((canonical odd).size == 196 && (canonical even).size == 164) "canonical calldata size changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (448 - MalformedBytes.programOverhead))
  let some plan := MalformedBytes.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some reference := LongBytes.CheckedPlan.ofStep? step | throw (IO.userError "the long-bytes wrapper failed admission")
  for (name, payload, malformation, expected) in cases do
    let tx := malformed payload malformation
    ensure (malformation.valid tx.payload (MalformedBytesExecution.canonicalBytes tx).size)
      s!"{name}: the malformation is outside its bounds"
    let history := MalformedBytesExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    checkExpected name reference (inputBytes tx) (← row history) expected fuel
  for (name, input, expected) in ordered do
    checkExpected name reference input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedBytesGolden
end

section
-- leanmerge: from Solcore.Test.SourceMalformedCalldataCases
/-! Malformed-calldata cases: generation is deterministic and validates every
prescribed std outcome against original Core; generated, imported and reduced
cases replay exactly; reductions remove transactions first and keep the G0
revision and swarm mask; the emitted source is the dynamic-array emission of
the same step; and the case boundary rejects malformations outside their
bounds, more than three elements and any calldata or std outcome that differs
from the malformation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedCalldataCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.MalformedCalldataExecution (Malformation Transaction)

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

def testSourceMalformedCalldataCases : IO Unit := do
  let corpus := MalformedCalldata.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8
  ensure (corpus == MalformedCalldata.generateCases (Seed.ofNat 1) 448 4 64 fuel .v3 8) "generation is nondeterministic"
  ensure ((← get (corpus.getObjValAs? String "status")) == "complete") "generation did not complete"
  let generated ← cases corpus
  let mut kinds : List String := []
  for saved in generated do
    ensure ((← get (MalformedCalldata.replayCase saved fuel)) == saved) "a generated case failed exact replay"
    let scenario ← get (MalformedCalldata.caseProgram saved)
    ensure (scenario.transactions.length == 8) "a generated case lost its requested length"
    kinds := (kinds ++ scenario.transactions.map (MalformedCalldata.kindOf ·.malformation)).eraseDups
    -- The compiled contract is the dynamic-array one.
    let emitted ← get (MalformedCalldata.emit scenario.plan)
    let some arrayPlan := Solcore.Synthesis.Core.DynamicArray.CheckedPlan.ofStep? scenario.plan.step
      | throw (IO.userError "the step failed dynamic-array admission")
    let array ← get ((DynamicArray.emit arrayPlan).mapError reprStr)
    ensure (emitted.source == array.source) "the emitted source differs from the dynamic-array emission"
  ensure (MalformedCalldata.malformationKinds.all kinds.contains) "generation misses a malformation kind"
  let some first := generated[0]? | throw (IO.userError "no generated case")
  let provenance ← get (first.getObjVal? "provenance")
  let reduced ← cases (← get (MalformedCalldata.shrinkCases first 24 fuel))
  let some removal := reduced[0]? | throw (IO.userError "a generated case has no reduction")
  let original ← get (first.getObjValAs? (List Json) "transactions")
  ensure ((← get (removal.getObjValAs? (List Json) "transactions")) == original.dropLast)
    "the first reduction does not remove the last transaction"
  for candidate in reduced do
    ensure ((← get (MalformedCalldata.replayCase candidate fuel)) == candidate) "a reduction failed exact replay"
    let candidateProvenance ← get (candidate.getObjVal? "provenance")
    ensure ((candidateProvenance.getObjVal? "swarmMask").toOption == (provenance.getObjVal? "swarmMask").toOption &&
      (candidateProvenance.getObjVal? "generatorVersion").toOption == (provenance.getObjVal? "generatorVersion").toOption)
      "a reduction lost the parent's revision or swarm mask"
  -- An imported sequence through the case boundary.
  let scenario ← get (MalformedCalldata.caseProgram first)
  let base : Transaction := ⟨"tx-0", w 2, [w 5, w 7], .none⟩
  let imported ← get (MalformedCalldata.checkedScenario scenario.plan
    [base, {base with id := "tx-1", malformation := .offset (w (2 ^ 256 - 4))}, {base with id := "tx-2", malformation := .trailing 1 2}])
  let importedCase ← get (MalformedCalldata.emitCase imported (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((← get (MalformedCalldata.replayCase importedCase fuel)) == importedCase) "an imported case failed exact replay"
  let rows ← get (importedCase.getObjValAs? (Array Json) "transactions")
  ensure ((rows.map fun row => (row.getObjVal? "stdRejection").toOption) ==
      #[some Json.null, some (toJson "0x08638556"), some Json.null]) "an imported case records other std outcomes"
  -- Malformations outside their bounds, more than three elements, too many
  -- transactions, and tampered calldata or std outcomes are rejected.
  for malformation in [Malformation.short 4, .selector 0, .selector (2 ^ 32), .truncate 3, .truncate 164,
      .trailing 0 0, .trailing 65 0, .trailing 1 3] do
    rejected (MalformedCalldata.checkedScenario scenario.plan [{base with malformation}])
      "a malformation outside its bounds was admitted"
  rejected (MalformedCalldata.checkedScenario scenario.plan [{base with values := [w 1, w 2, w 3, w 4]}])
    "four elements were admitted"
  rejected (MalformedCalldata.checkedScenario scenario.plan
    ((List.range (Solcore.Synthesis.Stateful.Sequence.maxTransactions + 1)).map fun index =>
      {base with id := "tx-" ++ toString index}))
    "an unbounded sequence was admitted"
  let row := rows[1]!
  for (key, value) in [("calldata", toJson "0x9a94c44b"), ("stdRejection", Json.null),
      ("stdRejection", toJson "0x4924aef0"), ("value", toJson "1")] do
    rejected (MalformedCalldata.decodeTransactions (toJson [row.setObjVal! key value]))
      s!"a transaction with a changed {key} was admitted"

end Tests.SourceMalformedCalldataCases
end

section
-- leanmerge: from Solcore.Test.SourceMalformedCalldataCorpus
/-! The fixed malformed-calldata corpus checks actual original Core histories
against expectations computed without the std-modeling wrapper: a prescribed
std rejection reverts with its selector Word and keeps the slots; an accepted
transaction is the canonical dynamic-array contract on the words std decodes.
Coverage describes the checked step AST, the canonical lengths and element
values, the malformation kinds, the prescribed std outcomes and the completions.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedCalldataCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", MalformedCalldata.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.MalformedCalldata.version),
  ("templateVersion", MalformedCalldata.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", MalformedCalldata.emitterVersion), ("wrapperVersion", MalformedCalldata.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The prescribed std outcomes, by name. -/
private def outcomeNames : List String :=
  ["0x4924aef0", "0x08638556", "accepted"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := MalformedCalldata.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← MalformedCalldata.checkedPlan (← entry.getObjVal? "malformedCalldataPlan")
  let scenario ← MalformedCalldata.checkedScenario plan
    (← MalformedCalldata.decodeTransactions (← entry.getObjVal? "transactions"))
  MalformedCalldata.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "malformed-calldata-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-malformed-calldata" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected malformed-calldata manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("malformed-calldata manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words MalformedCalldata.boundaryInputs))
    "malformed-calldata corpus must require all six boundary elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredLengths") == [0, 1, 2, 3])
    "malformed-calldata corpus must require lengths zero through three"
  require ((← strings manifest "requiredMalformations") == MalformedCalldata.malformationKinds)
    "malformed-calldata corpus must require every malformation kind"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "malformed-calldata corpus must require both std rejections and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "malformed-calldata corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "malformed-calldata corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "malformed-calldata corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "malformed-calldata corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "malformed-calldata corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut lengths : List Nat := []
  let mut kinds : List String := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate malformed-calldata corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← MalformedCalldata.replayCase saved fuel) == saved) ("malformed-calldata corpus entry did not replay: " ++ identifier)
    let scenario ← MalformedCalldata.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "malformedCalldataPlan") == (← entry.getObjVal? "malformedCalldataPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported malformed-calldata entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("malformed-calldata corpus features changed: " ++ identifier)
    let history := MalformedCalldata.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("malformed-calldata corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("malformed-calldata expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx => tx.values.map fun value => toString value.val).eraseDups
    lengths := (lengths ++ scenario.transactions.map (·.values.length)).eraseDups
    kinds := (kinds ++ scenario.transactions.map (MalformedCalldata.kindOf ·.malformation)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (MalformedCalldata.prescribed tx).map MalformedCalldata.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "malformed-calldata corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "malformed-calldata corpus misses a boundary element"
  require ([0, 1, 2, 3].all lengths.contains) "malformed-calldata corpus misses an array length"
  require (MalformedCalldata.malformationKinds.all kinds.contains) "malformed-calldata corpus misses a malformation kind"
  require (outcomeNames.all rejections.contains) "malformed-calldata corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "malformed-calldata corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "malformed-calldata corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "malformed-calldata corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-malformed-calldata"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("malformations", toJson kinds), ("rejections", toJson rejections),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid malformed-calldata corpus unexpectedly passed")

def testSourceMalformedCalldataCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-malformed-calldata-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first malformed-calldata case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated malformed-calldata case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- A std rejection's selector, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "none")])))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-dynamic-array"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredLengths", toJson [0, 1, 2]), ("requiredHelperCounts", toJson [1, 2]),
      ("requiredMalformations", toJson (["none"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMalformedCalldataCorpus
end

section
-- leanmerge: from Solcore.Test.SourceMalformedCalldataGolden
/-! Golden cases for the std model behind the malformed-calldata profile. The
expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol`, not computed by either model: a rejection
reverts with its error selector as a Word and keeps the empty storage; an
accepted malformation behaves exactly like the canonical dynamic-array
contract on the words std decodes. Both the Core wrapper and the byte-level
`stdRejection?` must give that outcome. Cases with two defects check std's
decode order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedCalldataGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedCalldataExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags and elements. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags : Nat) (values : List Nat)

private def noSelector : Expected := .rejected MalformedCalldata.noSelectorError
private def truncated : Expected := .rejected MalformedCalldata.truncatedError

/-- Canonical arguments: flags 2 (even, so the body returns) and the elements
5 and 7. The canonical calldata is 164 bytes: selector, flags, offset 64,
length 2 and the two elements. -/
private def flags : Nat := 2
private def values : List Nat := [5, 7]
private def size : Nat := 164

private def malformed (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w flags, values.map w, malformation⟩

private def cases : List (String × Malformation × Expected) := [
  ("canonical", .none, .accepted flags values),
  ("short-0", .short 0, noSelector), ("short-1", .short 1, noSelector), ("short-3", .short 3, noSelector),
  ("wrong-selector-low", .selector 1, noSelector), ("wrong-selector-high", .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", .selector (2 ^ 32 - 1), noSelector),
  -- Only the selector: the head check comes after dispatch.
  ("truncated-selector-only", .truncate 4, truncated),
  ("truncated-head-36", .truncate 36, truncated), ("truncated-head-67", .truncate 67, truncated),
  -- The head is complete but the length word is not.
  ("truncated-length", .truncate 99, truncated),
  -- The length is complete but the last element is not.
  ("truncated-element", .truncate (size - 1), truncated), ("truncated-last-word", .truncate (size - 32), truncated),
  ("trailing-1-zero", .trailing 1 0, .accepted flags values), ("trailing-33-ones", .trailing 33 1, .accepted flags values),
  ("trailing-64-ramp", .trailing 64 2, .accepted flags values),
  -- 161 > size - 4: the advance to the length word fails.
  ("offset-past-end", .offset (w (size - 3)), truncated),
  -- 129 <= size - 4, but only 31 bytes remain at 4 + 129.
  ("offset-partial-length", .offset (w (size - 35)), truncated),
  ("offset-high-bit", .offset (w (2 ^ 255)), truncated),
  -- 4 + o wraps to 0, 2 and 3; std compares o with size - 4 first.
  ("offset-wraps-to-0", .offset (w (2 ^ 256 - 4)), truncated),
  ("offset-wraps-to-2", .offset (w (2 ^ 256 - 2)), truncated),
  ("offset-wraps-to-3", .offset (w (2 ^ 256 - 1)), truncated),
  -- Offset 0: the length is the flags word, 2, and the elements are the words
  -- at 36 and 68, the replaced offset 0 and the original length 2.
  ("offset-overlaps-flags", .offset (w 0), .accepted flags [0, 2]),
  -- Offset 32: the length is the offset word itself, 32, and 1,024 element
  -- bytes do not fit.
  ("offset-overlaps-itself", .offset (w 32), truncated),
  ("length-one-too-long", .length (w 3), truncated),
  ("length-above-max", .length (w (2 ^ 251)), truncated),
  -- 32 * (2^251 + 1) wraps to 32 in Word arithmetic; std's bound check rejects first.
  ("length-product-wraps", .length (w (2 ^ 251 + 1)), truncated),
  ("length-maximum", .length (w (2 ^ 256 - 1)), truncated),
  ("length-one-shorter", .length (w 1), .accepted flags [5]),
  ("length-zero", .length (w 0), .accepted flags [])]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a truncated head: dispatch fails first.
  ("wrong-selector-and-short-head", bytes (selectorBytes (MalformedCalldata.selector ^^^ 1) ++ wordBytes flags),
    noSelector),
  -- Three bytes of the right selector are still short calldata.
  ("three-selector-bytes", bytes ((selectorBytes MalformedCalldata.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedCalldata.selector ++ wordBytes flags ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping offset and a wrapping length together: the offset is checked first.
  ("bad-offset-and-length", bytes (selectorBytes MalformedCalldata.selector ++ wordBytes flags ++
    wordBytes (2 ^ 256 - 4) ++ wordBytes (2 ^ 251 + 1)), truncated),
  -- The selector of another method with a canonical body is no match.
  ("other-selector-canonical-body", bytes (selectorBytes 0x7357f5d2 ++ wordBytes flags ++ wordBytes 64 ++
    wordBytes 0), noSelector)]

private def selectorOutput (selector : Nat) : String := encodeBytesText (encodeWordBytesBE (w selector))

private def row (history : Json) : IO Json := do
  let some first := (← get (history.getObjValAs? (Array Json) "transactions"))[0]?
    | throw (IO.userError "no transaction row")
  return first

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        match terminal.outcome with
        | .returned output => return Json.mkObj [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
        | .reverted output => return Json.mkObj [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
        | .trapped _ => return Json.mkObj [("status", toJson "trapped")]
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def checkExpected (name : String) (canonical : DynamicArray.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
  | .accepted expectedFlags expectedValues =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedCalldataExecution.stdDecoded? input == some (expectedFlags, expectedValues))
        s!"{name}: the byte model decodes other words"
      -- The canonical dynamic-array contract on the decoded words is the reference
      -- for the body. Elements past the third are never read.
      let reference := DynamicArrayExecution.observe canonical
        [⟨"tx-0", w expectedFlags, (expectedValues.take MalformedCalldata.maxElements).map w⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      if expectedValues.length ≤ MalformedCalldata.maxElements then
        for key in ["status", "output", "committedStorage", "accountStorage"] do
          ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
            s!"{name}: {key} differs from the canonical contract on the decoded words"

def testSourceMalformedCalldataGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedCalldata.selector == 0x9a94c44b) "the profile selector is not run(uint256,uint256[])"
  ensure ((DynamicArrayExecution.inputBytes (w flags) (values.map w)).size == size) "canonical calldata size changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (384 - MalformedCalldata.programOverhead))
  let some plan := MalformedCalldata.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some canonical := DynamicArray.CheckedPlan.ofStep? step | throw (IO.userError "the dynamic-array wrapper failed admission")
  for (name, malformation, expected) in cases do
    let tx := malformed malformation
    let history := MalformedCalldataExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    let outcome ← row history
    checkExpected name canonical (inputBytes tx) outcome expected fuel
    match expected with
    | .rejected _ =>
        ensure ((outcome.getObjVal? "committedStorage").toOption == (history.getObjVal? "initialStorage").toOption &&
          (outcome.getObjVal? "accountStorage").toOption == (history.getObjVal? "initialAccountStorage").toOption)
          s!"{name}: a std rejection changed storage"
    | .accepted _ _ => pure ()
  for (name, input, expected) in ordered do
    checkExpected name canonical input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedCalldataGolden
end

section
-- leanmerge: from Solcore.Test.SourceMalformedNestedArrayCases
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
end

section
-- leanmerge: from Solcore.Test.SourceMalformedNestedArrayCorpus
/-! The fixed malformed-nested-array corpus checks actual original Core
histories against expectations computed without the std-modeling wrapper: a
prescribed std rejection reverts with its selector Word and keeps the slots; an
accepted transaction is the canonical nested-array contract on the Words std
decodes. Coverage describes the checked step AST, the canonical outer and row
lengths and element values, the malformation kinds and the rows they target,
the prescribed std outcomes and the completions. Source/Rust/EVM agreement is a
separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceMalformedNestedArrayCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let values ← value.getObjValAs? (List String) key
  require (values.eraseDups == values) (key ++ " contains duplicates")
  return values

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", MalformedNestedArray.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.MalformedNestedArray.version),
  ("templateVersion", MalformedNestedArray.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", MalformedNestedArray.emitterVersion), ("wrapperVersion", MalformedNestedArray.wrapperVersion)]

private def words (values : List Word) : List String := values.map fun value => toString value.val

/-- The prescribed std outcomes, by name. -/
private def outcomeNames : List String :=
  ["0x4924aef0", "0x08638556", "accepted"]

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := MalformedNestedArray.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let plan ← MalformedNestedArray.checkedPlan (← entry.getObjVal? "malformedNestedArrayPlan")
  let scenario ← MalformedNestedArray.checkedScenario plan
    (← MalformedNestedArray.decodeTransactions (← entry.getObjVal? "transactions"))
  MalformedNestedArray.emitCase scenario (Json.mkObj [("kind", toJson "imported")]) fuel

private def templates (saved : Json) : Except String (List Nat) := do
  let origin ← (← saved.getObjVal? "provenance").getObjVal? "origin"
  if (← string origin "kind") != "malformed-nested-array-generated" then return []
  let helpers ← (← origin.getObjVal? "stepOrigin").getObjValAs? (List Json) "helpers"
  helpers.mapM fun helper => helper.getObjValAs? Nat "template"

def validateManifest (manifest : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-malformed-nested-array" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected malformed-nested-array manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("malformed-nested-array manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (words MalformedNestedArray.boundaryInputs))
    "malformed-nested-array corpus must require all six boundary elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredRowCounts") == [0, 1, 2, 3, 4] &&
    (← manifest.getObjValAs? (List Nat) "requiredRowLengths") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require zero to four rows of zero to three elements"
  require ((← manifest.getObjValAs? (List Nat) "requiredMalformedRows") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require row malformations of rows zero to three"
  require ((← strings manifest "requiredMalformations") == MalformedNestedArray.malformationKinds)
    "malformed-nested-array corpus must require every malformation kind"
  require ((← strings manifest "requiredRejections") == outcomeNames)
    "malformed-nested-array corpus must require both std rejections and acceptance"
  require ((← manifest.getObjValAs? (List Nat) "requiredHelperCounts") == [1, 2, 3] &&
    (← manifest.getObjValAs? (List Nat) "requiredTransactionCounts") == [1, 2, 3])
    "malformed-nested-array corpus must require one to three helpers and transactions"
  require ((← (← manifest.getObjVal? "generationRecipeRequirements").getObjValAs? (List Nat) "templates") == [0, 1, 2, 3])
    "malformed-nested-array corpus must require all four step templates"
  require ((← strings manifest "requiredOutcomes") == ["returned", "reverted"])
    "malformed-nested-array corpus must require both outcomes"
  let requiredPatterns ← strings manifest "requiredCompletionPatterns"
  require (!requiredPatterns.isEmpty) "malformed-nested-array corpus must require completion patterns"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 64) "malformed-nested-array corpus must contain 1..64 scenarios"
  let mut identifiers : List String := []
  let mut features : List String := []
  let mut inputs : List String := []
  let mut rowCounts : List Nat := []
  let mut rowLengths : List Nat := []
  let mut malformedRows : List Nat := []
  let mut kinds : List String := []
  let mut rejections : List String := []
  let mut helperCounts : List Nat := []
  let mut transactionCounts : List Nat := []
  let mut templateUnion : List Nat := []
  let mut outcomes : List String := []
  let mut patterns : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate malformed-nested-array corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← MalformedNestedArray.replayCase saved fuel) == saved) ("malformed-nested-array corpus entry did not replay: " ++ identifier)
    let scenario ← MalformedNestedArray.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "malformedNestedArrayPlan") == (← entry.getObjVal? "malformedNestedArrayPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported malformed-nested-array entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    require (sameMembers (← strings entry "expectedFeatures") caseFeatures)
      ("malformed-nested-array corpus features changed: " ++ identifier)
    let history := MalformedNestedArray.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("malformed-nested-array corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("malformed-nested-array expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expectation without the std wrapper: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    transactionTotal := transactionTotal + observed.length
    features := (features ++ caseFeatures).eraseDups
    inputs := (inputs ++ scenario.transactions.flatMap fun tx =>
      tx.values.flatMap fun row => row.map fun value => toString value.val).eraseDups
    rowCounts := (rowCounts ++ scenario.transactions.map (·.values.length)).eraseDups
    rowLengths := (rowLengths ++ scenario.transactions.flatMap fun tx => tx.values.map (·.length)).eraseDups
    malformedRows := (malformedRows ++ scenario.transactions.filterMap (MalformedNestedArray.rowOf ·.malformation)).eraseDups
    kinds := (kinds ++ scenario.transactions.map (MalformedNestedArray.kindOf ·.malformation)).eraseDups
    rejections := (rejections ++ scenario.transactions.map fun tx =>
      (MalformedNestedArray.prescribed tx).map MalformedNestedArray.selectorText |>.getD "accepted").eraseDups
    helperCounts := (helperCounts ++ [scenario.plan.step.helpers.length]).eraseDups
    transactionCounts := (transactionCounts ++ [scenario.transactions.length]).eraseDups
    templateUnion := (templateUnion ++ (← templates saved)).eraseDups
    outcomes := (outcomes ++ statuses).eraseDups
    patterns := (patterns ++ [String.intercalate "," statuses]).eraseDups
  require (requiredFeatures.all features.contains) "malformed-nested-array corpus misses a required step feature"
  require (requiredInputs.all inputs.contains) "malformed-nested-array corpus misses a boundary element"
  require ([0, 1, 2, 3, 4].all rowCounts.contains && [0, 1, 2, 3].all rowLengths.contains)
    "malformed-nested-array corpus misses an outer or row length"
  require ([0, 1, 2, 3].all malformedRows.contains) "malformed-nested-array corpus misses a malformed row"
  require (MalformedNestedArray.malformationKinds.all kinds.contains) "malformed-nested-array corpus misses a malformation kind"
  require (outcomeNames.all rejections.contains) "malformed-nested-array corpus misses a std outcome"
  require ([1, 2, 3].all helperCounts.contains && [1, 2, 3].all transactionCounts.contains)
    "malformed-nested-array corpus misses a helper or transaction count"
  require ([0, 1, 2, 3].all templateUnion.contains) "malformed-nested-array corpus misses a generated template"
  require (["returned", "reverted"].all outcomes.contains && requiredPatterns.all patterns.contains)
    "malformed-nested-array corpus misses an observed outcome or completion pattern"
  return Json.mkObj [("profile", toJson "stateful-malformed-nested-array"), ("scenarios", toJson entries.size),
    ("transactions", toJson transactionTotal), ("malformations", toJson kinds), ("rejections", toJson rejections),
    ("patterns", toJson patterns)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid malformed-nested-array corpus unexpectedly passed")

def testSourceMalformedNestedArrayCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-malformed-nested-array-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first malformed-nested-array case")
  let some generatedEntry := entries.find? (fun entry => (entry.getObjVal? "generation").isOk) |
    throw (IO.userError "missing generated malformed-nested-array case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  -- A std rejection's selector, a slot, a missing row and a status are all checked.
  let changedOutput := row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedOutput)))))
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  let changedSlot := row.setObjVal! "committedStorage" (.arr (storage.set! 0 (storage[0]!.setObjVal! "value" (toJson "7"))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changedSlot)))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr (history.pop)))))
  let generatedHistory ← checked (generatedEntry.getObjValAs? (Array Json) "expectedHistory")
  let flipped := if (generatedHistory[0]!.getObjValAs? String "status").toOption == some "returned" then "reverted" else "returned"
  rejects (validateManifest (replace generatedEntry (generatedEntry.setObjVal! "expectedHistory"
    (.arr (generatedHistory.set! 0 (generatedHistory[0]!.setObjVal! "status" (toJson flipped)))))))
  let transactions ← checked (first.getObjValAs? (Array Json) "transactions")
  rejects (validateManifest (replace first (first.setObjVal! "transactions"
    (.arr (transactions.set! 0 (transactions[0]!.setObjVal! "malformation" (Json.mkObj [("kind", toJson "none")])))))))
  rejects (validateManifest (replace first (first.setObjVal! "expectedFeatures" (toJson ([] : List String)))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))))
  for (key, value) in [
      ("profile", toJson "stateful-nested-array"), ("templateVersion", toJson "forged"),
      ("cases", .arr #[]), ("requiredInputs", toJson ([] : List String)),
      ("requiredRowCounts", toJson [0, 1, 2, 3]), ("requiredMalformedRows", toJson [0, 1, 2]),
      ("requiredHelperCounts", toJson [1, 2]),
      ("requiredMalformations", toJson (["none"] : List String)),
      ("requiredRejections", toJson (["accepted"] : List String)),
      ("requiredCompletionPatterns", toJson (["returned,returned,returned,returned"] : List String))] do
    rejects (validateManifest (manifest.setObjVal! key value))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourceMalformedNestedArrayCorpus
end

section
-- leanmerge: from Solcore.Test.SourceMalformedNestedArrayGolden
/-! Golden cases for the std model behind the malformed-nested-array profile.
The expected outcome of every case is written out from the pinned std's
`dispatch.sol` and `std.sol`, not computed by either model: a rejection
reverts with its error selector as a Word and keeps the empty storage; an
accepted malformation behaves exactly like the canonical nested-array contract
on the Words std decodes. Both the Core wrapper and the byte-level `stdDecode`
must give that outcome. Cases on four rows check std's lazy row checks, and
cases with two defects check its decode order. -/
set_option autoImplicit false

namespace Tests.SourceMalformedNestedArrayGolden

open Lean
open Solcore.Core (Word)
open Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Stateful.MalformedNestedArrayExecution (Malformation Transaction inputBytes stdRejection?)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The expected std outcome: the rejecting selector, or acceptance with the
decoded flags, outer length and the elements of every row the body reads. -/
private inductive Expected where
  | rejected (selector : Nat)
  | accepted (flags rows : Nat) (read : List (List Nat))

private def noSelector : Expected := .rejected StdDispatch.noSelectorError
private def truncated : Expected := .rejected StdDispatch.truncatedError

/-- Three rows, flags 2 (even, so the body returns). The calldata is 388
bytes: the head, the outer length 3 at byte 68, the table at 100 with the
Words 96, 192 and 256, then row zero at 196 (length 2, elements 1 and 4 at 228
and 260), row one at 292 (length 1, element 9 at 324) and the empty row two at
356. -/
private def three : List (List Nat) := [[1, 4], [9], []]
/-- Two rows: the table Words 64 and 160, row zero at 164, row one at 260; 324 bytes. -/
private def two : List (List Nat) := [[1, 4], [9]]
/-- Four rows: the table Words 128, 192, 224 and 352, row zero at 228 (length
1, element 3), the empty row one at 292, row two at 324 (length 3, elements 7,
1 and 0 at 356, 388 and 420) and row three at 452 (length 1, element 1 at
484); 516 bytes. The body never reads row three or row two's third element. -/
private def four : List (List Nat) := [[3], [], [7, 1, 0], [1]]

private def malformed (values : List (List Nat)) (malformation : Malformation) : Transaction :=
  ⟨"tx-0", w 2, values.map (·.map w), malformation⟩

private def cases : List (String × List (List Nat) × Malformation × Expected) := [
  ("canonical", three, .none, .accepted 2 3 three),
  ("short-0", three, .short 0, noSelector), ("short-1", three, .short 1, noSelector),
  ("short-3", three, .short 3, noSelector),
  ("wrong-selector-low", three, .selector 1, noSelector),
  ("wrong-selector-high", three, .selector (2 ^ 31), noSelector),
  ("wrong-selector-all", three, .selector (2 ^ 32 - 1), noSelector),
  ("truncated-selector-only", three, .truncate 4, truncated),
  ("truncated-head", three, .truncate 67, truncated),
  -- 31 bytes remain at 4 + 64.
  ("truncated-outer-length", three, .truncate 99, truncated),
  -- The table needs 96 bytes at 100; 16 remain.
  ("truncated-table", three, .truncate 116, truncated),
  -- Row zero's elements need 64 bytes at 228; 63 remain.
  ("truncated-first-row", three, .truncate 291, truncated),
  -- Row two's length Word at 356 has 31 bytes.
  ("truncated-last-row", three, .truncate 387, truncated),
  ("trailing-1-zero", three, .trailing 1 0, .accepted 2 3 three),
  ("trailing-33-ones", three, .trailing 33 1, .accepted 2 3 three),
  ("trailing-64-ramp", three, .trailing 64 2, .accepted 2 3 three),
  ("offset-past-end", three, .offset (w 385), truncated),
  ("offset-partial-length", three, .offset (w 353), truncated),
  ("offset-high-bit", three, .offset (w (2 ^ 255)), truncated),
  ("offset-wraps", three, .offset (w (2 ^ 256 - 4)), truncated),
  -- Offset 0: the outer length is the flags Word, 2, and the table starts at
  -- 36. Its first Word, the offset 0 itself, makes row zero start at 36 with
  -- length 0. Its second Word, the original outer length 3, makes row one
  -- start at 39, where the Word holds bytes 39 to 70, all zero.
  ("offset-overlaps-flags", three, .offset (w 0), .accepted 2 2 [[], []]),
  -- Offset 32: the outer length is the offset Word, 32, and a 1,024-byte table does not fit.
  ("offset-overlaps-itself", three, .offset (w 32), truncated),
  -- A fourth table Word, row zero's length 2, which the body never reads.
  ("length-unread-extra-row", three, .length (w 4), .accepted 2 4 three),
  ("length-above-max", three, .length (w (2 ^ 251)), truncated),
  -- 32 * (2^251 + 1) wraps to 32 in Word arithmetic; std's bound check rejects first.
  ("length-product-wraps", three, .length (w (2 ^ 251 + 1)), truncated),
  ("length-maximum", three, .length (w (2 ^ 256 - 1)), truncated),
  ("length-one-shorter", three, .length (w 2), .accepted 2 2 two),
  ("length-zero", three, .length (w 0), .accepted 2 0 []),
  -- A third table Word, row zero's length 2, which the body reads: row two
  -- starts at 102, where the Word holds the low bytes of the table Word 64
  -- and is 64 * 2^16, far too long.
  ("length-read-extra-row", two, .length (w 3), truncated),
  -- 289 > size - T = 288.
  ("row-offset-past-end", three, .rowOffset 1 (w 289), truncated),
  -- 288 is in range, but no length Word remains at 388.
  ("row-offset-at-end", three, .rowOffset 1 (w 288), truncated),
  ("row-offset-partial-length", three, .rowOffset 1 (w 257), truncated),
  ("row-offset-high-bit", three, .rowOffset 1 (w (2 ^ 255)), truncated),
  -- T + r would wrap onto the outer length Word at 68.
  ("row-offset-wraps-onto-outer-length", three, .rowOffset 1 (w (2 ^ 256 - 32)), truncated),
  ("row-offset-maximum", three, .rowOffset 1 (w (2 ^ 256 - 1)), truncated),
  -- Row zero starts at its own table Word, now 0, and is empty.
  ("row-offset-own-entry", three, .rowOffset 0 (w 0), .accepted 2 3 [[], [9], []]),
  -- Row one starts at the table: its length is the table Word 96, which does not fit.
  ("row-offset-into-table", three, .rowOffset 1 (w 0), truncated),
  ("row-offset-aliases-row", three, .rowOffset 1 (w 96), .accepted 2 3 [[1, 4], [1, 4], []]),
  -- Row one starts at row zero's first element, 1, so its element is row zero's second, 4.
  ("row-offset-inside-row", three, .rowOffset 1 (w 128), .accepted 2 3 [[1, 4], [4], []]),
  -- Row zero runs into row one's length Word.
  ("row-length-one-too-long", three, .rowLength 0 (w 3), .accepted 2 3 [[1, 4, 1], [9], []]),
  ("row-length-most-that-fits", three, .rowLength 0 (w 5), .accepted 2 3 [[1, 4, 1, 9, 0], [9], []]),
  ("row-length-one-past-fit", three, .rowLength 0 (w 6), truncated),
  ("row-length-last-row", three, .rowLength 2 (w 1), truncated),
  ("row-length-above-max", three, .rowLength 1 (w (2 ^ 251)), truncated),
  ("row-length-product-wraps", three, .rowLength 1 (w (2 ^ 251 + 1)), truncated),
  ("row-length-maximum", three, .rowLength 1 (w (2 ^ 256 - 1)), truncated),
  ("row-length-one-shorter", three, .rowLength 0 (w 1), .accepted 2 3 [[1], [9], []]),
  ("row-length-zero", three, .rowLength 0 (w 0), .accepted 2 3 [[], [9], []]),
  -- Lazy checks on four rows.
  ("four-rows", four, .none, .accepted 2 4 (four.take 3)),
  ("unread-row-offset", four, .rowOffset 3 (w (2 ^ 256 - 1)), .accepted 2 4 (four.take 3)),
  ("unread-row-length", four, .rowLength 3 (w (2 ^ 256 - 1)), .accepted 2 4 (four.take 3)),
  ("cut-inside-unread-row", four, .truncate 515, .accepted 2 4 (four.take 3)),
  ("cut-unread-row-length", four, .truncate 468, .accepted 2 4 (four.take 3)),
  -- The table is checked whole, including row three's Word.
  ("cut-inside-table", four, .truncate 212, truncated),
  -- Row two's region is checked whole, including the third element the body skips.
  ("cut-skipped-element", four, .truncate 451, truncated),
  ("row-length-into-unread-row", four, .rowLength 2 (w 4), .accepted 2 4 [[3], [], [7, 1, 0, 1]]),
  -- Row one is checked after row zero has been folded and written; nothing commits.
  ("second-row-after-first", four, .rowOffset 1 (w (2 ^ 256 - 32)), truncated)]

/-- Raw calldata with two defects at once, for the decode order. -/
private def bytes (parts : List Nat) : ByteArray := ByteArray.mk (parts.map Nat.toUInt8).toArray

private def selectorBytes (selector : Nat) : List Nat :=
  [selector / 2 ^ 24 % 256, selector / 2 ^ 16 % 256, selector / 2 ^ 8 % 256, selector % 256]

private def wordBytes (value : Nat) : List Nat := (encodeWordBytesBE (w value)).data.toList.map UInt8.toNat

private def canonical (values : List (List Nat)) : ByteArray :=
  NestedArrayExecution.inputBytes (w 2) (values.map (·.map w))

private def replaced (input : ByteArray) (changes : List (Nat × Nat)) : ByteArray :=
  changes.foldl (fun bytes (position, value) => StdCalldata.replaceWord bytes position (w value)) input

private def ordered : List (String × ByteArray × Expected) := [
  -- A wrong selector wins over a malformed row: dispatch fails first.
  ("wrong-selector-and-bad-row",
    replaced ((StdCalldata.Change.selector 1).apply (canonical three)) [(132, 2 ^ 256 - 1)], noSelector),
  -- Three bytes of the right selector are still short calldata.
  ("three-selector-bytes", bytes ((selectorBytes MalformedNestedArray.selector).take 3), noSelector),
  -- A truncated head wins over a bad offset in the bytes that are present.
  ("short-head-and-bad-offset", bytes (selectorBytes MalformedNestedArray.selector ++ wordBytes 2 ++
    (wordBytes (2 ^ 256 - 4)).take 31), truncated),
  -- A wrapping head offset and a wrapping row offset: the outer array is checked first.
  ("bad-offset-and-row", replaced (canonical three) [(36, 2 ^ 256 - 4), (132, 2 ^ 256 - 1)], truncated),
  -- An outer length of 2 leaves row two unread, so its maximal length is never checked.
  ("row-unread-by-length", replaced (canonical three) [(68, 2), (356, 2 ^ 256 - 1)], .accepted 2 2 two),
  -- Row zero overlaps its own table Word and is accepted; row one is then rejected.
  ("accepted-row-then-bad-row", replaced (canonical three) [(100, 0), (132, 2 ^ 256 - 32)], truncated),
  -- The dynamic-array selector with a canonical nested body is no match.
  ("other-selector-canonical-body",
    bytes (selectorBytes 0x9a94c44b) ++ (canonical three).extract 4 (canonical three).size, noSelector)]

private def selectorOutput (selector : Nat) : String := encodeBytesText (encodeWordBytesBE (w selector))

private def row (history : Json) : IO Json := do
  let some first := (← get (history.getObjValAs? (Array Json) "transactions"))[0]?
    | throw (IO.userError "no transaction row")
  return first

/-- The original Core contract run once from an empty world on raw calldata. -/
private def runRaw (contract : CheckedCoreContract) (input : ByteArray) (fuel : Nat) : IO Json := do
  let bindings := StorageExecution.fixtureBindings
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let world := StorageExecution.initialWorldForContract contract bindings
  let some ⟨resolved, installed⟩ := registry.resolve? world bindings.address
    | throw (IO.userError "contract does not resolve")
  if bounded : input.size < Solcore.Core.wordModulus then
    let invocation : TopLevelInvocation := {
      target := bindings.address, caller := bindings.caller, callValue := Word.zero,
      inputData := ⟨input, bounded⟩ }
    match TopLevelExecution.run resolved invocation installed fuel with
    | .completed terminal =>
        let storage := match terminal.finalWorld.account? bindings.address with
          | some account => NestedArrayExecution.storageJson account
          | none => Json.null
        let fields := match terminal.outcome with
          | .returned output => [("status", toJson "returned"), ("output", toJson (encodeBytesText output))]
          | .reverted output => [("status", toJson "reverted"), ("output", toJson (encodeBytesText output))]
          | .trapped _ => [("status", toJson "trapped")]
        return Json.mkObj (fields ++ [("committedStorage", storage),
          ("accountStorage", AccountStorage.contractJson terminal.finalWorld bindings.address)])
    | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "golden case exhausted fuel")
  else throw (IO.userError "golden input exceeds a Word")

private def checkExpected (name : String) (canonical : NestedArray.CheckedPlan)
    (input : ByteArray) (outcome : Json) (expected : Expected) (fuel : Nat) : IO Unit := do
  match expected with
  | .rejected selector =>
      ensure (stdRejection? input == some selector) s!"{name}: the byte model does not reject with {selector}"
      ensure ((← get (outcome.getObjValAs? String "status")) == "reverted" &&
        (← get (outcome.getObjValAs? String "output")) == selectorOutput selector)
        s!"{name}: original Core does not revert with the std selector"
      -- Nothing commits: storage stays empty.
      let empty := NestedArrayExecution.observe canonical [] StorageExecution.fixtureBindings fuel
      ensure ((outcome.getObjVal? "committedStorage").toOption == (empty.getObjVal? "initialStorage").toOption &&
        (outcome.getObjVal? "accountStorage").toOption == (empty.getObjVal? "initialAccountStorage").toOption)
        s!"{name}: a std rejection changed storage"
  | .accepted flags rows read =>
      ensure (stdRejection? input == none) s!"{name}: the byte model rejects an accepted malformation"
      ensure (MalformedNestedArrayExecution.stdDecoded? input == some (flags, rows, read))
        s!"{name}: the byte model decodes other Words"
      -- The canonical nested-array contract on the decoded Words is the reference
      -- for the body. Rows past the third are never read, so they stay empty.
      let values : List (List Word) := (read ++ List.replicate (rows - read.length) ([] : List Nat)).map (·.map w)
      let reference := NestedArrayExecution.observe canonical [⟨"tx-0", w flags, values⟩]
        StorageExecution.fixtureBindings fuel
      let referenceRow ← row reference
      for key in ["status", "output", "committedStorage", "accountStorage"] do
        ensure ((outcome.getObjVal? key).toOption == (referenceRow.getObjVal? key).toOption)
          s!"{name}: {key} differs from the canonical contract on the decoded Words"

def testSourceMalformedNestedArrayGolden : IO Unit := do
  let fuel := 1000000
  ensure (MalformedNestedArray.selector == 0x7095aff8) "the profile selector is not run(uint256,uint256[][])"
  for (values, size) in [(three, 388), (two, 324), (four, 516)] do
    ensure ((canonical values).size == size) "canonical calldata size changed"
  ensure (MalformedNestedArrayExecution.rowStart (four.map (·.map w)) 3 == 452) "row positions changed"
  let (step, _) ← get (Solcore.Synthesis.Source.Aggregate.generatedFunction (Seed.ofNat 1)
    (448 - MalformedNestedArray.programOverhead))
  let some plan := MalformedNestedArray.CheckedPlan.ofStep? step | throw (IO.userError "the std wrapper failed admission")
  let some reference := NestedArray.CheckedPlan.ofStep? step | throw (IO.userError "the nested-array wrapper failed admission")
  for (name, values, malformation, expected) in cases do
    let tx := malformed values malformation
    ensure (malformation.valid tx.values (MalformedNestedArrayExecution.canonicalBytes tx).size)
      s!"{name}: the malformation is outside its bounds"
    let history := MalformedNestedArrayExecution.observe plan [tx] StorageExecution.fixtureBindings fuel
    checkExpected name reference (inputBytes tx) (← row history) expected fuel
  for (name, input, expected) in ordered do
    checkExpected name reference input (← runRaw plan.contract input fuel) expected fuel

end Tests.SourceMalformedNestedArrayGolden
end
