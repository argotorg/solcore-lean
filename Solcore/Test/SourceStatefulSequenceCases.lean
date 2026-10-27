import Solcore.Synthesis.Source.StorageCases
import Solcore.Synthesis.Source.StorageRollbackCases
import Solcore.Synthesis.Source.NestedCallCases
import Solcore.Synthesis.Source.KeyedStorageCases
import Solcore.Synthesis.Source.DynamicArrayCases
import Solcore.Synthesis.Source.EventLogCases
import Solcore.Synthesis.Source.CallValueCases
import Solcore.Synthesis.Source.DynamicBytesCases
import Solcore.Synthesis.Source.ForwardedCallCases
import Solcore.Synthesis.Source.StorageMappingCases
import Solcore.Synthesis.Source.StorageLedgerCases
import Solcore.Synthesis.Source.LongBytesCases
import Solcore.Synthesis.Source.NestedArrayCases

/-! Every stateful profile generates a requested sequence length as the first
transactions of its consecutive three-transaction blocks, records any length
other than three, replays exactly that length and first removes the last
transaction when it shrinks. The existing case tests and fixed corpora pin the
three-transaction default. -/
set_option autoImplicit false

namespace Tests.SourceStatefulSequenceCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source
open Solcore.Synthesis.Stateful.Sequence (maxTransactions blockSeeds)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Nat → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json

private def profiles : List Profile := [
  ⟨"stateful-storage", fun seed nodes count attempts fuel revision transactions =>
      Storage.generateCases seed nodes count attempts fuel revision transactions,
    Storage.replayCase, Storage.shrinkCases⟩,
  ⟨"stateful-storage-rollback", fun seed nodes count attempts fuel revision transactions =>
      StorageRollback.generateCases seed nodes count attempts fuel revision transactions,
    StorageRollback.replayCase, StorageRollback.shrinkCases⟩,
  ⟨"stateful-calls", fun seed nodes count attempts fuel revision transactions =>
      NestedCall.generateCases seed nodes count attempts fuel revision transactions,
    NestedCall.replayCase, NestedCall.shrinkCases⟩,
  ⟨"stateful-keyed-storage", fun seed nodes count attempts fuel revision transactions =>
      KeyedStorage.generateCases seed nodes count attempts fuel revision transactions,
    KeyedStorage.replayCase, KeyedStorage.shrinkCases⟩,
  ⟨"stateful-dynamic-array", fun seed nodes count attempts fuel revision transactions =>
      DynamicArray.generateCases seed nodes count attempts fuel revision transactions,
    DynamicArray.replayCase, DynamicArray.shrinkCases⟩,
  ⟨"stateful-logs", fun seed nodes count attempts fuel revision transactions =>
      EventLog.generateCases seed nodes count attempts fuel revision transactions,
    EventLog.replayCase, EventLog.shrinkCases⟩,
  ⟨"stateful-call-value", fun seed nodes count attempts fuel revision transactions =>
      CallValue.generateCases seed nodes count attempts fuel revision transactions,
    CallValue.replayCase, CallValue.shrinkCases⟩,
  ⟨"stateful-bytes", fun seed nodes count attempts fuel revision transactions =>
      DynamicBytes.generateCases seed nodes count attempts fuel revision transactions,
    DynamicBytes.replayCase, DynamicBytes.shrinkCases⟩,
  ⟨"stateful-forwarded-value", fun seed nodes count attempts fuel revision transactions =>
      ForwardedCall.generateCases seed nodes count attempts fuel revision transactions,
    ForwardedCall.replayCase, ForwardedCall.shrinkCases⟩,
  ⟨"stateful-mapping", fun seed nodes count attempts fuel revision transactions =>
      StorageMapping.generateCases seed nodes count attempts fuel revision transactions,
    StorageMapping.replayCase, StorageMapping.shrinkCases⟩,
  ⟨"stateful-ledger", fun seed nodes count attempts fuel revision transactions =>
      StorageLedger.generateCases seed nodes count attempts fuel revision transactions,
    StorageLedger.replayCase, StorageLedger.shrinkCases⟩,
  ⟨"stateful-long-bytes", fun seed nodes count attempts fuel revision transactions =>
      LongBytes.generateCases seed nodes count attempts fuel revision transactions,
    LongBytes.replayCase, LongBytes.shrinkCases⟩,
  ⟨"stateful-nested-array", fun seed nodes count attempts fuel revision transactions =>
      NestedArray.generateCases seed nodes count attempts fuel revision transactions,
    NestedArray.replayCase, NestedArray.shrinkCases⟩]

private def fuel : Nat := 1000000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def firstCase (corpus : Json) (name : String) : IO Json := do
  let some case := (← cases corpus)[0]? | throw (IO.userError s!"{name}: generation produced no case")
  return case

private def transactions (case : Json) : IO (List Json) :=
  get (case.getObjValAs? (List Json) "transactions")

private def origin (case : Json) : IO Json := do
  get ((← get (case.getObjVal? "provenance")).getObjVal? "origin")

private def withOrigin (case : Json) (origin : Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" origin)

private def ids (rows : List Json) : IO (List String) :=
  rows.mapM fun row => get (row.getObjValAs? String "id")

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun (seed attempts count : Nat) => profile.generate (Seed.ofNat seed) 384 1 attempts fuel .v2 count
  let short ← firstCase (generate 11 64 3) profile.name
  ensure ((← origin short).getObjVal? "transactionCount" matches .error _)
    s!"{profile.name}: a three-transaction origin records its count"
  -- Longer and shorter sequences start at the short case's seed, so their
  -- first block is the short sequence.
  let some seed := (← get ((← origin short).getObjValAs? String "seed")).toNat?
    | throw (IO.userError s!"{profile.name}: invalid saved seed")
  let single ← firstCase (generate seed 1 1) profile.name
  ensure ((← transactions single) == (← transactions short).take 1) s!"{profile.name}: one transaction is not the first"
  let long ← firstCase (generate seed 1 maxTransactions) profile.name
  let rows ← transactions long
  ensure ((← ids rows) == (List.range maxTransactions).map (fun index => "tx-" ++ toString index))
    s!"{profile.name}: a long sequence has the wrong transaction IDs"
  ensure (rows.take 3 == (← transactions short)) s!"{profile.name}: a long sequence does not extend the short one"
  ensure (((← origin long).getObjValAs? Nat "transactionCount").toOption == some maxTransactions)
    s!"{profile.name}: a long origin does not record its count"
  ensure ((← cases (generate seed 1 (maxTransactions + 1))).isEmpty) s!"{profile.name}: an unbounded sequence was generated"
  ensure ((← get (profile.replay long fuel)) == long) s!"{profile.name}: a long case failed exact replay"
  for recorded in [3, maxTransactions - 1, maxTransactions + 1] do
    let changed ← withOrigin long ((← origin long).setObjVal! "transactionCount" (toJson recorded))
    ensure (profile.replay changed fuel matches .error _)
      s!"{profile.name}: a long case replayed with transaction count {recorded}"
  let reduced ← cases (← get (profile.shrink long 4 fuel))
  let some first := reduced[0]? | throw (IO.userError s!"{profile.name}: a long case has no reduction")
  ensure ((← transactions first) == rows.dropLast) s!"{profile.name}: reduction does not first remove the last transaction"
  for candidate in reduced do
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a long reduction failed exact replay"

/-- Generated values and amounts keep their totals; three transactions never
reach them. -/
private def checkValueBounds : IO Unit := do
  let large := Word.ofNatModulo (2 ^ 70)
  let sent := (List.range 8).map fun index =>
    ({id := "tx-" ++ toString index, flags := Word.zero, input := Word.zero, value := large} :
      Solcore.Synthesis.Stateful.CallValueExecution.Transaction)
  ensure ((CallValue.boundedValues (Word.ofNatModulo 5) sent).map (·.value.val) ==
      [2 ^ 70, 2 ^ 70, 2 ^ 70, 0, 0, 0, 0, 0]) "call values exceed the funded total"
  ensure (CallValue.boundedValues (Word.ofNatModulo 5) (sent.take 3) == sent.take 3) "three call values were bounded"
  let forwarded := (List.range 8).map fun index =>
    ({id := "tx-" ++ toString index, input := Word.zero, value := large, amount := large} :
      Solcore.Synthesis.Stateful.ForwardedCallExecution.Transaction)
  ensure ((ForwardedCall.boundedAmounts forwarded).map (·.amount.val) == [2 ^ 70, 2 ^ 70, 2 ^ 70, 2 ^ 70, 0, 0, 0, 0])
    "forwarded amounts exceed the endowment"
  ensure ((ForwardedCall.boundedAmounts forwarded).map (·.value.val) == List.replicate 8 (2 ^ 70))
    "bounding forwarded amounts changed a call value"

def testSourceStatefulSequenceCases : IO Unit := do
  ensure (profiles.length == 13) "a stateful profile is missing from the sequence checks"
  ensure ((blockSeeds (Seed.ofNat 7) 3).head? == some (Seed.ofNat 7)) "block zero no longer uses the scenario seed"
  ensure ((blockSeeds (Seed.ofNat 7) 3).eraseDups.length == 3) "block seeds repeat"
  checkValueBounds
  for profile in profiles do
    checkProfile profile

end Tests.SourceStatefulSequenceCases
