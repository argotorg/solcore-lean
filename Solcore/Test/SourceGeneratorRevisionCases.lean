import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases

/-! Every G0-based case profile generates, records, replays and reduces cases
of either G0 revision. Generation without a revision keeps `v1`, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceGeneratorRevisionCases

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
  nodes : Nat
  count : Nat
  /-- The provenance fields that name the G0 revision. -/
  versions : GeneratorRevision → List (String × String)

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  ⟨"closed-g0", fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replayCase, shrinkCases, 24, 2, g0Version⟩,
  ⟨"runtime-word", fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    Input.replayCase, Input.shrinkCases, 32, 4, g0Version⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    Primitive.replayCase, Primitive.shrinkCases, 96, 8, fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision),
       ("baseGeneratorVersion", revision.version)]⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel revision =>
      Function.generateCases seed nodes count attempts fuel revision,
    Function.replayCase, Function.shrinkCases, 64, 4, g0Version⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    Mutation.replayCase, Mutation.shrinkCases, 192, 4, g0Version⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    Aggregate.replayCase, Aggregate.shrinkCases, 256, 4, g0Version⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    Loop.replayCase, Loop.shrinkCases, 384, 6, g0Version⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    Generic.replayCase, Generic.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    Closure.replayCase, Closure.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    Comptime.replayCase, Comptime.shrinkCases, 384, 4, g0Version⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    Modules.replayCase, Modules.shrinkCases, 384, 4, g0Version⟩]

private def fuel : Nat := 100000

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def records (profile : Profile) (revision : GeneratorRevision) (case : Json) : IO Bool := do
  let saved ← provenance case
  return (profile.versions revision).all fun (name, version) =>
    (saved.getObjValAs? String name).toOption == some version

private def withVersions (case : Json) (fields : List (String × String)) : IO Json := do
  let saved ← provenance case
  return case.setObjVal! "provenance"
    (fields.foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved)

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v2)
  ensure (generate .v2 == generate .v2) s!"{profile.name}: v2 generation is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: v2 generation did not complete"
  let original ← cases (generate .v1)
  ensure (original.size == profile.count) s!"{profile.name}: v1 generation did not complete"
  for case in original do
    ensure (← records profile .v1 case) s!"{profile.name}: v1 case lost its version"
  ensure (current != original) s!"{profile.name}: v2 reproduced the v1 cases"
  for case in current do
    ensure (← records profile .v2 case) s!"{profile.name}: v2 case does not record its version"
    ensure ((← get (profile.replay case fuel)) == case)
      s!"{profile.name}: v2 case failed exact replay"
    -- Replaying under the other revision regenerates a different program.
    ensure (profile.replay (← withVersions case (profile.versions .v1)) fuel matches .error _)
      s!"{profile.name}: a v2 case replayed as v1"
    let unknown := (profile.versions .v2).map fun (name, _) => (name, "core-g0-v3/lcg64-v1")
    ensure (profile.replay (← withVersions case unknown) fuel matches .error _)
      s!"{profile.name}: an unknown G0 version replayed"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no v2 case")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: v2 case has no reduction candidate"
  for candidate in reduced do
    ensure (← records profile .v2 candidate)
      s!"{profile.name}: a reduction lost the parent's G0 revision"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a v2 reduction failed exact replay"

def testSourceGeneratorRevisionCases : IO Unit := do
  ensure (profiles.length == 11) "a G0-based profile is missing from the revision checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceGeneratorRevisionCases
