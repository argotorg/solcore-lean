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

/-! Every stateful profile generates its checked step with any G0 revision,
records it, replays it and passes it to its reductions, together with revision
three's swarm mask. Generation without a revision keeps `v1`, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceStatefulGeneratorRevisionCases

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → GeneratorRevision → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json

private def profiles : List Profile := [
  ⟨"stateful-storage", fun seed nodes count attempts fuel revision =>
      Storage.generateCases seed nodes count attempts fuel revision, Storage.replayCase, Storage.shrinkCases⟩,
  ⟨"stateful-storage-rollback", fun seed nodes count attempts fuel revision =>
      StorageRollback.generateCases seed nodes count attempts fuel revision,
    StorageRollback.replayCase, StorageRollback.shrinkCases⟩,
  ⟨"stateful-calls", fun seed nodes count attempts fuel revision =>
      NestedCall.generateCases seed nodes count attempts fuel revision, NestedCall.replayCase, NestedCall.shrinkCases⟩,
  ⟨"stateful-keyed-storage", fun seed nodes count attempts fuel revision =>
      KeyedStorage.generateCases seed nodes count attempts fuel revision,
    KeyedStorage.replayCase, KeyedStorage.shrinkCases⟩,
  ⟨"stateful-dynamic-array", fun seed nodes count attempts fuel revision =>
      DynamicArray.generateCases seed nodes count attempts fuel revision,
    DynamicArray.replayCase, DynamicArray.shrinkCases⟩,
  ⟨"stateful-logs", fun seed nodes count attempts fuel revision =>
      EventLog.generateCases seed nodes count attempts fuel revision, EventLog.replayCase, EventLog.shrinkCases⟩,
  ⟨"stateful-call-value", fun seed nodes count attempts fuel revision =>
      CallValue.generateCases seed nodes count attempts fuel revision, CallValue.replayCase, CallValue.shrinkCases⟩,
  ⟨"stateful-bytes", fun seed nodes count attempts fuel revision =>
      DynamicBytes.generateCases seed nodes count attempts fuel revision,
    DynamicBytes.replayCase, DynamicBytes.shrinkCases⟩,
  ⟨"stateful-forwarded-value", fun seed nodes count attempts fuel revision =>
      ForwardedCall.generateCases seed nodes count attempts fuel revision,
    ForwardedCall.replayCase, ForwardedCall.shrinkCases⟩,
  ⟨"stateful-mapping", fun seed nodes count attempts fuel revision =>
      StorageMapping.generateCases seed nodes count attempts fuel revision,
    StorageMapping.replayCase, StorageMapping.shrinkCases⟩,
  ⟨"stateful-ledger", fun seed nodes count attempts fuel revision =>
      StorageLedger.generateCases seed nodes count attempts fuel revision,
    StorageLedger.replayCase, StorageLedger.shrinkCases⟩,
  ⟨"stateful-long-bytes", fun seed nodes count attempts fuel revision =>
      LongBytes.generateCases seed nodes count attempts fuel revision, LongBytes.replayCase, LongBytes.shrinkCases⟩,
  ⟨"stateful-nested-array", fun seed nodes count attempts fuel revision =>
      NestedArray.generateCases seed nodes count attempts fuel revision,
    NestedArray.replayCase, NestedArray.shrinkCases⟩]

private def fuel : Nat := 1000000

private def recordedVersion (case : Json) : IO String := do
  get ((← get (case.getObjVal? "provenance")).getObjValAs? String "generatorVersion")

private def withVersion (case : Json) (version : String) : IO Json := do
  let saved ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (saved.setObjVal! "generatorVersion" (toJson version))

private def firstCase (corpus : Json) (name : String) : IO Json := do
  let some case := (← get (corpus.getObjValAs? (Array Json) "cases"))[0]?
    | throw (IO.userError s!"{name}: generation produced no case")
  return case

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision => profile.generate (Seed.ofNat 5) 384 1 64 fuel revision
  let current ← firstCase (generate .v2) profile.name
  ensure (generate .v2 == generate .v2) s!"{profile.name}: v2 generation is not deterministic"
  let original ← firstCase (generate .v1) profile.name
  ensure ((← recordedVersion original) == GeneratorRevision.v1.version) s!"{profile.name}: v1 case lost its version"
  ensure ((← recordedVersion current) == GeneratorRevision.v2.version) s!"{profile.name}: v2 case does not record its version"
  ensure (current != original) s!"{profile.name}: v2 reproduced the v1 scenario"
  ensure ((← get (profile.replay current fuel)) == current) s!"{profile.name}: v2 case failed exact replay"
  -- Replaying under the other revision regenerates a different step.
  ensure (profile.replay (← withVersion current GeneratorRevision.v1.version) fuel matches .error _)
    s!"{profile.name}: a v2 case replayed as v1"
  ensure (profile.replay (← withVersion current "core-g0-v9/lcg64-v1") fuel matches .error _)
    s!"{profile.name}: an unknown G0 version replayed"
  let reduced ← get ((← get (profile.shrink current 2 fuel)).getObjValAs? (Array Json) "cases")
  ensure (!reduced.isEmpty) s!"{profile.name}: v2 case has no reduction candidate"
  for candidate in reduced do
    ensure ((← recordedVersion candidate) == GeneratorRevision.v2.version)
      s!"{profile.name}: a reduction lost the parent's G0 revision"
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a v2 reduction failed exact replay"

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

/-- Revision three records the scenario seed's swarm mask, which every helper
of the step uses. Replay requires and checks it, the other revisions refuse
one, and reductions copy it. -/
private def checkMask (profile : Profile) : IO Unit := do
  let generate := fun revision => profile.generate (Seed.ofNat 5) 384 1 64 fuel revision
  ensure (generate .v3 == generate .v3) s!"{profile.name}: v3 generation is not deterministic"
  let masked ← firstCase (generate .v3) profile.name
  let plain ← firstCase (generate .v2) profile.name
  ensure ((← provenance plain).getObjVal? "swarmMask" matches .error _) s!"{profile.name}: a v2 case records a swarm mask"
  ensure ((← recordedVersion masked) == GeneratorRevision.v3.version) s!"{profile.name}: v3 case does not record its version"
  let saved ← provenance masked
  let some seed := (← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")).toNat?
    | throw (IO.userError s!"{profile.name}: invalid saved seed")
  let mask := GeneratorRevision.v3.caseMask (Seed.ofNat seed)
  ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask)
    s!"{profile.name}: a v3 case does not record the mask of its seed"
  ensure ((← get (profile.replay masked fuel)) == masked) s!"{profile.name}: v3 case failed exact replay"
  ensure (profile.replay (← withProvenance masked withoutMask) fuel matches .error _)
    s!"{profile.name}: a v3 case replayed without its mask"
  let changed := toJson ((mask.enabled.drop 1).map featureName)
  ensure (profile.replay (← withProvenance masked (·.setObjVal! "swarmMask" changed)) fuel matches .error _)
    s!"{profile.name}: a changed swarm mask replayed"
  ensure (profile.replay (← withVersion masked GeneratorRevision.v2.version) fuel matches .error _)
    s!"{profile.name}: a swarm mask replayed under revision two"
  let reduced ← get ((← get (profile.shrink masked 2 fuel)).getObjValAs? (Array Json) "cases")
  ensure (!reduced.isEmpty) s!"{profile.name}: v3 case has no reduction candidate"
  for candidate in reduced do
    ensure (((← provenance candidate).getObjVal? "swarmMask").toOption == some (maskJson mask))
      s!"{profile.name}: a reduction lost the parent's swarm mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate) s!"{profile.name}: a v3 reduction failed exact replay"

def testSourceStatefulGeneratorRevisionCases : IO Unit := do
  ensure (profiles.length == 13) "a stateful profile is missing from the revision checks"
  for profile in profiles do
    checkProfile profile
    checkMask profile

end Tests.SourceStatefulGeneratorRevisionCases
