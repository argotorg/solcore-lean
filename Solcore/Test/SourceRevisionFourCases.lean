import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.NestedLoopCases
import Solcore.Synthesis.Source.RecursionCases
import Solcore.Synthesis.Source.RecursiveLoopCases
import Solcore.Synthesis.Source.LoopClosureCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.AssemblyCases
import Solcore.Synthesis.Source.AssemblyMemoryCases

/-! Revision-four cases of every G0-based profile record their case seed's
swarm mask restricted to the features of the profile's emitter, use no other
feature, replay exactly, refuse a mask outside those features and pass the
mask to their reductions. Where the emitter renders every feature, revision
four is revision three apart from its version. -/
set_option autoImplicit false

namespace Tests.SourceRevisionFourCases

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
  /-- The features of the emitter that renders the case's recorded mask. -/
  support : FeatureMask
  /-- The features of the comptime and module constants' own renderer. -/
  constant : Option FeatureMask := none
  /-- Whether every recorded feature comes from G0 alone, without a template. -/
  scalar : Bool := false

private def g0Version (revision : GeneratorRevision) : List (String × String) :=
  [("generatorVersion", revision.version)]

private def profiles : List Profile := [
  {name := "closed-g0", generate := fun seed nodes count attempts fuel revision =>
      generateCases seed nodes count attempts fuel revision,
    replay := replayCase, shrink := shrinkCases, nodes := 24, count := 2, versions := g0Version,
    support := featureSupport, scalar := true},
  {name := "runtime-word", generate := fun seed nodes count attempts fuel revision =>
      Input.generateCases seed nodes count attempts fuel revision,
    replay := Input.replayCase, shrink := Input.shrinkCases, nodes := 32, count := 4, versions := g0Version,
    support := Input.featureSupport, scalar := true},
  {name := "runtime-primitives", generate := fun seed nodes count attempts fuel revision =>
      Primitive.generateCases seed nodes count attempts fuel revision,
    replay := Primitive.replayCase, shrink := Primitive.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := Primitive.featureSupport, scalar := true},
  {name := "runtime-assembly", generate := fun seed nodes count attempts fuel revision =>
      Assembly.generateCases seed nodes count attempts fuel revision,
    replay := Assembly.replayCase, shrink := Assembly.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := Assembly.featureSupport, scalar := true},
  {name := "runtime-assembly-memory", generate := fun seed nodes count attempts fuel revision =>
      AssemblyMemory.generateCases seed nodes count attempts fuel revision,
    replay := AssemblyMemory.replayCase, shrink := AssemblyMemory.shrinkCases, nodes := 96, count := 8,
    versions := fun revision =>
      [("generatorVersion", Primitive.generatorVersionFor revision), ("baseGeneratorVersion", revision.version)],
    support := AssemblyMemory.featureSupport, scalar := true},
  {name := "runtime-functions", generate := fun seed nodes count attempts fuel revision =>
      Solcore.Synthesis.Source.Function.generateCases seed nodes count attempts fuel revision,
    replay := Solcore.Synthesis.Source.Function.replayCase, shrink := Solcore.Synthesis.Source.Function.shrinkCases,
    nodes := 64, count := 4, versions := g0Version, support := Solcore.Synthesis.Source.Function.featureSupport},
  {name := "runtime-mutation", generate := fun seed nodes count attempts fuel revision =>
      Mutation.generateCases seed nodes count attempts fuel revision,
    replay := Mutation.replayCase, shrink := Mutation.shrinkCases, nodes := 192, count := 4,
    versions := g0Version, support := Mutation.featureSupport},
  {name := "runtime-aggregates", generate := fun seed nodes count attempts fuel revision =>
      Aggregate.generateCases seed nodes count attempts fuel revision,
    replay := Aggregate.replayCase, shrink := Aggregate.shrinkCases, nodes := 256, count := 4,
    versions := g0Version, support := Aggregate.featureSupport},
  {name := "runtime-loops", generate := fun seed nodes count attempts fuel revision =>
      Loop.generateCases seed nodes count attempts fuel revision,
    replay := Loop.replayCase, shrink := Loop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := Loop.featureSupport},
  {name := "runtime-nested-loops", generate := fun seed nodes count attempts fuel revision =>
      NestedLoop.generateCases seed nodes count attempts fuel revision,
    replay := NestedLoop.replayCase, shrink := NestedLoop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := NestedLoop.featureSupport},
  {name := "runtime-recursion", generate := fun seed nodes count attempts fuel revision =>
      Recursion.generateCases seed nodes count attempts fuel revision,
    replay := Recursion.replayCase, shrink := Recursion.shrinkCases, nodes := 384, count := 7,
    versions := g0Version, support := Recursion.featureSupport},
  {name := "runtime-recursive-loops", generate := fun seed nodes count attempts fuel revision =>
      RecursiveLoop.generateCases seed nodes count attempts fuel revision,
    replay := RecursiveLoop.replayCase, shrink := RecursiveLoop.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := RecursiveLoop.featureSupport},
  {name := "runtime-loop-closures", generate := fun seed nodes count attempts fuel revision =>
      LoopClosure.generateCases seed nodes count attempts fuel revision,
    replay := LoopClosure.replayCase, shrink := LoopClosure.shrinkCases, nodes := 384, count := 6,
    versions := g0Version, support := LoopClosure.featureSupport},
  {name := "runtime-generics", generate := fun seed nodes count attempts fuel revision =>
      Generic.generateCases seed nodes count attempts fuel revision,
    replay := Generic.replayCase, shrink := Generic.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Generic.featureSupport},
  {name := "runtime-closures", generate := fun seed nodes count attempts fuel revision =>
      Closure.generateCases seed nodes count attempts fuel revision,
    replay := Closure.replayCase, shrink := Closure.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Closure.featureSupport},
  {name := "runtime-comptime", generate := fun seed nodes count attempts fuel revision =>
      Comptime.generateCases seed nodes count attempts fuel revision,
    replay := Comptime.replayCase, shrink := Comptime.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Comptime.featureSupport, constant := some Comptime.constantSupport},
  {name := "runtime-modules", generate := fun seed nodes count attempts fuel revision =>
      Modules.generateCases seed nodes count attempts fuel revision,
    replay := Modules.replayCase, shrink := Modules.shrinkCases, nodes := 384, count := 4,
    versions := g0Version, support := Modules.featureSupport, constant := some Modules.constantSupport}]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def provenance (case : Json) : IO Json := get (case.getObjVal? "provenance")

private def withProvenance (case : Json) (change : Json → Json) : IO Json := do
  return case.setObjVal! "provenance" (change (← provenance case))

private def withoutMask : Json → Json
  | .obj fields => .obj (fields.erase "swarmMask")
  | other => other

private def relabel (profile : Profile) (revision : GeneratorRevision) (case : Json) : IO Json :=
  withProvenance case fun saved =>
    (profile.versions revision).foldl (fun json (name, version) => json.setObjVal! name (toJson version)) saved

private def catalogName (name : String) : Bool := FeatureMask.catalog.any (featureName · = name)

/-- Every recorded catalog feature is allowed; leaves and template features are not catalog features. -/
private def within (mask : FeatureMask) (names : List String) : Bool :=
  names.all fun name => !catalogName name || mask.enabled.any (featureName · = name)

private def checkProfile (profile : Profile) : IO Unit := do
  let generate := fun revision =>
    profile.generate (Seed.ofNat 11) profile.nodes profile.count 64 fuel revision
  let current ← cases (generate .v4)
  ensure (generate .v4 == generate .v4) s!"{profile.name}: revision four is not deterministic"
  ensure (current.size == profile.count) s!"{profile.name}: revision-four generation did not complete"
  if profile.support == FeatureMask.all && profile.constant.isNone then
    let three ← cases (generate .v3)
    ensure ((← current.mapM (relabel profile .v3)) == three)
      s!"{profile.name}: revision four differs from revision three although its emitter renders every feature"
  for case in current do
    let saved ← provenance case
    let seedText ← get ((← get (saved.getObjVal? "origin")).getObjValAs? String "seed")
    let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
    let mask := GeneratorRevision.v4.caseMask (Seed.ofNat seed) profile.support
    ensure ((← get (saved.getObjVal? "swarmMask")) == maskJson mask && mask.subset profile.support)
      s!"{profile.name}: a case does not record its seed's mask restricted to its emitter"
    let features ← get (saved.getObjValAs? (List String) "features")
    ensure (within (if profile.scalar then mask else profile.support) features)
      s!"{profile.name}: a case uses a feature outside its mask or its emitter"
    if let some constant := profile.constant then
      let constantFeatures ← get (saved.getObjValAs? (List String) "constantFeatures")
      ensure (within (mask.within constant) constantFeatures)
        s!"{profile.name}: a constant uses a feature outside its renderer's restriction of the mask"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a revision-four case failed exact replay"
    ensure (profile.replay (← withProvenance case withoutMask) fuel matches .error _)
      s!"{profile.name}: a revision-four case replayed without its mask"
    let other := GeneratorRevision.v4.caseMask (Seed.ofNat (seed + 1)) profile.support
    if other != mask then
      ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" (maskJson other))) fuel matches .error _)
        s!"{profile.name}: another seed's mask replayed"
    if profile.support != FeatureMask.all then
      ensure (profile.replay (← withProvenance case (·.setObjVal! "swarmMask" (maskJson FeatureMask.all))) fuel
          matches .error _)
        s!"{profile.name}: a mask outside its emitter's features replayed"
    -- Under revision three's label a case replays with revision three's mask
    -- only. A comptime or module constant is restricted further, so there an
    -- equal recorded mask decides nothing.
    let downgraded ← relabel profile .v3 case
    if mask != GeneratorRevision.v3.caseMask (Seed.ofNat seed) then
      ensure (profile.replay downgraded fuel matches .error _)
        s!"{profile.name}: a revision-four case replayed under revision three with another mask"
    else if profile.constant.isNone then
      ensure (profile.replay downgraded fuel matches .ok _)
        s!"{profile.name}: a revision-four case with revision three's mask is not revision three's case"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no revision-four case")
  let parentMask ← get ((← provenance first).getObjVal? "swarmMask")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a revision-four case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get ((← provenance candidate).getObjVal? "swarmMask")) == parentMask)
      s!"{profile.name}: a reduction lost its parent's mask"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a revision-four case failed exact replay"

private def unsupportedExclusions (corpus : Json) : IO Nat := do
  let excluded ← get (corpus.getObjValAs? (Array Json) "excluded")
  return (excluded.filter fun entry =>
    match entry.getObjValAs? String "reason" with
    | .ok reason => (reason.splitOn "EmitError.unsupported").length > 1
    | .error _ => false).size

private def distinctSources (corpus : Json) : IO Nat := do
  let sources ← (← cases corpus).toList.mapM fun case => get (case.getObjValAs? String "source")
  return sources.eraseDups.length

/-- From seed one, revision four never generates a program the emitter rejects,
and `runtime-word` accepts its functions with far fewer attempts and repeats. -/
private def statisticsChecks : IO Unit := do
  for profile in profiles do
    if profile.support != FeatureMask.all || profile.constant.isSome then
      let corpus := profile.generate (Seed.ofNat 1) profile.nodes (16 * profile.count) 4096 fuel .v4
      ensure ((← cases corpus).size == 16 * profile.count) s!"{profile.name}: revision four exhausted generation"
      ensure ((← unsupportedExclusions corpus) == 0)
        s!"{profile.name}: revision four generated a program its emitter rejects"
  let word := fun revision => Input.generateCases (Seed.ofNat 1) 32 256 4096 fuel revision
  let attempted := fun (corpus : Json) => get (corpus.getObjValAs? Nat "attempted")
  let (three, four) := (word .v3, word .v4)
  ensure (2 * (← attempted four) ≤ (← attempted three))
    s!"runtime-word: revision four needed {← attempted four} attempts against {← attempted three}"
  ensure ((← distinctSources four) ≥ 3 * (← distinctSources three))
    s!"runtime-word: revision four has {← distinctSources four} sources against {← distinctSources three}"

def testSourceRevisionFourCases : IO Unit := do
  ensure (profiles.length == 17) "a G0-based profile is missing from the revision-four checks"
  for profile in profiles do
    checkProfile profile
  statisticsChecks

end Tests.SourceRevisionFourCases
