import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases

/-! Revision-three cases of every G0-based profile record the swarm mask of
their case seed, replay it exactly and pass it to their reductions. Cases of
the other revisions record no mask. -/
set_option autoImplicit false

namespace Tests.SourceSwarmMaskCases

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
  /-- The provenance version fields of a revision. -/
  versions : GeneratorRevision → List (String × String)
  /-- Whether every recorded feature comes from G0 alone, without a template. -/
  scalar : Bool

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  ⟨"closed-g0", fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replayCase, shrinkCases, 24, 2, g0Version, true⟩,
  ⟨"runtime-word", fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    Input.replayCase, Input.shrinkCases, 32, 4, g0Version, true⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    Primitive.replayCase, Primitive.shrinkCases, 96, 8, fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision),
       ("baseGeneratorVersion", revision.version)], true⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel revision =>
      Function.generateCases seed nodes count attempts fuel revision,
    Function.replayCase, Function.shrinkCases, 64, 4, g0Version, false⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    Mutation.replayCase, Mutation.shrinkCases, 192, 4, g0Version, false⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    Aggregate.replayCase, Aggregate.shrinkCases, 256, 4, g0Version, false⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    Loop.replayCase, Loop.shrinkCases, 384, 6, g0Version, false⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    Generic.replayCase, Generic.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    Closure.replayCase, Closure.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    Comptime.replayCase, Comptime.shrinkCases, 384, 4, g0Version, false⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    Modules.replayCase, Modules.shrinkCases, 384, 4, g0Version, false⟩]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

private def leaves : List String := ["wordLiteral", "local", "boolLiteral"]

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v3)
  ensure (generate .v3 == generate .v3) s!"{profile.name}: revision three is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: revision-three generation did not complete"
  for case in ← cases (generate .v2) do
    ensure ((← provenance case).getObjVal? "swarmMask" matches .error _)
      s!"{profile.name}: a revision-two case records a swarm mask"
  for case in current do
    let saved ← provenance case
    let seedText ← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")
    let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
    let mask := GeneratorRevision.v3.caseMask (Seed.ofNat seed)
    ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask)
      s!"{profile.name}: a case does not record the mask of its seed"
    if profile.scalar then
      let allowed := leaves ++ mask.enabled.map featureName
      let features ← get (saved.getObjValAs? (List String) "features")
      ensure (features.all allowed.contains) s!"{profile.name}: a case uses a feature its mask disables"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a masked case failed exact replay"
    ensure (profile.replay (← withProvenance case withoutMask) fuel matches .error _)
      s!"{profile.name}: a revision-three case replayed without its mask"
    let shrunk := toJson ((mask.enabled.drop 1).map featureName)
    ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" shrunk)) fuel matches .error _)
      s!"{profile.name}: a changed mask replayed"
    let downgraded ← withProvenance case fun saved =>
      (profile.versions .v2).foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved
    ensure (profile.replay downgraded fuel matches .error _)
      s!"{profile.name}: a mask replayed under revision two"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no masked case")
  let parentMask ← get ((← provenance first).getObjVal? "swarmMask")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a masked case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get ((← provenance candidate).getObjVal? "swarmMask")) == parentMask)
      s!"{profile.name}: a reduction lost its parent's mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a masked case failed exact replay"

def testSourceSwarmMaskCases : IO Unit := do
  ensure (profiles.length == 11) "a G0-based profile is missing from the swarm mask checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceSwarmMaskCases
