import Solcore.Synthesis.Source.FunctionCases
import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.AggregateCases
import Solcore.Synthesis.Source.LoopCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.PrimitiveCases
import Solcore.Synthesis.Source.CallGraphCases
import Solcore.Synthesis.Source.CallGraphLoopCases
import Solcore.Synthesis.Source.AggregateCallGraphCases

/-! Seeded runtime inputs: their replay vectors and value ranges, and their
generation, recording, replay, tampering and reduction in every runtime-input
profile. Generation without a selection keeps the boundary inputs, which the
existing case tests and fixed corpora pin. -/
set_option autoImplicit false

namespace Tests.SourceSeededInputCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def seeded (seed : Nat) : List Nat :=
  (InputSelection.seededInputs (Seed.ofNat seed)).map (·.val)

private def vectorChecks : IO Unit := do
  ensure (seeded 0 == [
      56189052813837018966195966706874179130487732287838569029762288915300383936473,
      15797683219724309265658083358374668, 106, 2 ^ 256 - 6])
    "the seeded input vector of seed 0 changed"
  ensure (seeded 4254 == [
      87847550103885626486316609148408507170101340273028280478259265334201237472442,
      37415062808491099348759069756, 470, 0])
    "the seeded input vector of seed 4254 changed"
  ensure (InputSelection.ofVersion? InputSelection.seededVersion == some .seeded &&
      InputSelection.seededVersion == "seeded-inputs-v1/splitmix64" &&
      InputSelection.ofVersion? "core-g0-v2/lcg64-v1" == none)
    "the seeded input version changed"
  let boundaries := Input.boundaryInputs
  ensure (InputSelection.boundary.inputs boundaries (Seed.ofNat 9) == boundaries &&
      InputSelection.seeded.inputs boundaries (Seed.ofNat 9) ==
        boundaries ++ InputSelection.seededInputs (Seed.ofNat 9))
    "a selection changed its boundary prefix"
  let origin := Json.mkObj [("kind", toJson "input-generated")]
  ensure (InputSelection.boundary.record origin == origin &&
      (InputSelection.ofOrigin origin).toOption == some .boundary &&
      (InputSelection.ofOrigin (InputSelection.seeded.record origin)).toOption == some .seeded)
    "an origin does not round-trip its selection"
  for value in [toJson "seeded-inputs-v2/splitmix64", toJson (1 : Nat)] do
    ensure (InputSelection.ofOrigin (origin.setObjVal! "inputSelection" value) matches .error _)
      "an unknown input selection was accepted"

/-- Bit length; zero has length zero. -/
private def bits (value : Nat) : Nat :=
  if value = 0 then 0 else Nat.log2 value + 1

/-- 2,048 consecutive seeds: each slot keeps its range and spreads within it. -/
private def rangeChecks : IO Unit := do
  let samples := (List.range 2048).map seeded
  let slot := fun (index : Nat) => samples.map (·.getD index 0)
  ensure (samples.all (·.length == 4)) "a seed did not give four inputs"
  let full := slot 0
  let high := (full.filter (· ≥ 2 ^ 255)).length
  ensure (900 ≤ high && high ≤ 1148) s!"full random inputs set the top bit {high} times of 2048"
  let widths := (slot 1).map bits
  ensure (widths.any (· ≤ 8) && widths.any (fun width => 64 < width && width ≤ 128) &&
      widths.any (· > 248)) "uniform-width inputs miss small, middle or full widths"
  let small := slot 2
  ensure (small.all (· < 512) && small.eraseDups.length > 400 && small.any (· < 32) &&
      small.any (· ≥ 256)) "small inputs leave their range or cluster"
  let negated := slot 3
  let negative := (negated.filter (· ≥ 2 ^ 255)).length
  ensure (negative ≥ 2000 && negated.any (· ≥ 2 ^ 256 - 256))
    s!"negated inputs are negative {negative} times of 2048 or never near -1"

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → InputSelection → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  boundaries : List Word
  nodes : Nat

/-- G0-based profiles run with revision two, as random campaigns do. -/
private def profiles : List Profile := [
  ⟨"runtime-word", fun seed nodes count attempts fuel inputs =>
      Input.generateCases seed nodes count attempts fuel .v2 inputs,
    Input.replayCase, Input.shrinkCases, Input.boundaryInputs, 32⟩,
  ⟨"runtime-primitives", fun seed nodes count attempts fuel inputs =>
      Primitive.generateCases seed nodes count attempts fuel .v2 inputs,
    Primitive.replayCase, Primitive.shrinkCases, Primitive.boundaryInputs, 96⟩,
  ⟨"runtime-functions", fun seed nodes count attempts fuel inputs =>
      Function.generateCases seed nodes count attempts fuel .v2 inputs,
    Function.replayCase, Function.shrinkCases, Input.boundaryInputs, 64⟩,
  ⟨"runtime-mutation", fun seed nodes count attempts fuel inputs =>
      Mutation.generateCases seed nodes count attempts fuel .v2 inputs,
    Mutation.replayCase, Mutation.shrinkCases, Input.boundaryInputs, 192⟩,
  ⟨"runtime-aggregates", fun seed nodes count attempts fuel inputs =>
      Aggregate.generateCases seed nodes count attempts fuel .v2 inputs,
    Aggregate.replayCase, Aggregate.shrinkCases, Input.boundaryInputs, 256⟩,
  ⟨"runtime-loops", fun seed nodes count attempts fuel inputs =>
      Loop.generateCases seed nodes count attempts fuel .v2 inputs,
    Loop.replayCase, Loop.shrinkCases, Loop.boundaryInputs, 384⟩,
  ⟨"runtime-generics", fun seed nodes count attempts fuel inputs =>
      Generic.generateCases seed nodes count attempts fuel .v2 inputs,
    Generic.replayCase, Generic.shrinkCases, Generic.boundaryInputs, 384⟩,
  ⟨"runtime-closures", fun seed nodes count attempts fuel inputs =>
      Closure.generateCases seed nodes count attempts fuel .v2 inputs,
    Closure.replayCase, Closure.shrinkCases, Closure.boundaryInputs, 384⟩,
  ⟨"runtime-comptime", fun seed nodes count attempts fuel inputs =>
      Comptime.generateCases seed nodes count attempts fuel .v2 inputs,
    Comptime.replayCase, Comptime.shrinkCases, Comptime.boundaryInputs, 384⟩,
  ⟨"runtime-modules", fun seed nodes count attempts fuel inputs =>
      Modules.generateCases seed nodes count attempts fuel .v2 inputs,
    Modules.replayCase, Modules.shrinkCases, Modules.boundaryInputs, 384⟩,
  ⟨"runtime-call-graphs", fun seed nodes count attempts fuel inputs =>
      CallGraph.generateCases seed nodes count attempts fuel inputs,
    CallGraph.replayCase, CallGraph.shrinkCases, CallGraph.boundaryInputs, 192⟩,
  ⟨"runtime-call-graph-loops", fun seed nodes count attempts fuel inputs =>
      CallGraphLoop.generateCases seed nodes count attempts fuel inputs,
    CallGraphLoop.replayCase, CallGraphLoop.shrinkCases, CallGraphLoop.boundaryInputs, 256⟩,
  ⟨"runtime-aggregate-call-graphs", fun seed nodes count attempts fuel inputs =>
      AggregateCallGraph.generateCases seed nodes count attempts fuel inputs,
    AggregateCallGraph.replayCase, AggregateCallGraph.shrinkCases, AggregateCallGraph.boundaryInputs, 192⟩]

private def fuel : Nat := 100000

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def origin (case : Json) : IO Json :=
  get ((case.getObjVal? "provenance").bind (·.getObjVal? "origin"))

private def withOrigin (case : Json) (origin : Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" origin)

private def withoutSelection : Json → Json
  | .obj fields => .obj (fields.erase "inputSelection")
  | other => other

private def checkProfile (profile : Profile) : IO Unit := do
  let count := profile.boundaries.length + 4
  let generate := fun inputs => profile.generate (Seed.ofNat 31) profile.nodes count 64 fuel inputs
  let current ← cases (generate .seeded)
  ensure (generate .seeded == generate .seeded) s!"{profile.name}: seeded generation is not deterministic"
  ensure (current.size == count) s!"{profile.name}: one function did not give every seeded input"
  let some first := current[0]? | throw (IO.userError s!"{profile.name}: no seeded case")
  let seedText ← get ((← origin first).getObjValAs? String "seed")
  let some seed := seedText.toNat? | throw (IO.userError s!"{profile.name}: invalid seed")
  let inputs ← current.toList.mapM fun case => get (case.getObjValAs? String "input")
  ensure (inputs == (InputSelection.seeded.inputs profile.boundaries (Seed.ofNat seed)).map
      (toString ·.val)) s!"{profile.name}: inputs are not the boundaries followed by the seeded inputs"
  -- Boundary selection gives the same first cases, only without the selection.
  let original ← cases (generate .boundary)
  let boundaryCases ← (current.extract 0 profile.boundaries.length).mapM fun case => do
    withOrigin case (withoutSelection (← origin case))
  ensure (original.extract 0 profile.boundaries.length == boundaryCases)
    s!"{profile.name}: seeded selection changed a boundary case"
  for case in current do
    ensure ((← get ((← origin case).getObjValAs? String "inputSelection")) == InputSelection.seededVersion)
      s!"{profile.name}: a seeded case does not name its selection"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a seeded case failed exact replay"
  let some last := current.back? | throw (IO.userError s!"{profile.name}: no seeded case")
  let lastOrigin ← origin last
  ensure (profile.replay (← withOrigin last (withoutSelection lastOrigin)) fuel matches .error _)
    s!"{profile.name}: a seeded input replayed without its selection"
  ensure (profile.replay (← withOrigin last (lastOrigin.setObjVal! "inputSelection"
      (toJson "seeded-inputs-v2/splitmix64"))) fuel matches .error _)
    s!"{profile.name}: an unknown input selection replayed"
  let forged := last.setObjVal! "input" (toJson "12345")
  ensure (profile.replay forged fuel matches .error _) s!"{profile.name}: a changed seeded input replayed"
  let reduced ← cases (← get (profile.shrink last 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a seeded case has no reduction candidate"
  for candidate in reduced do
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a seeded case failed exact replay"

def testSourceSeededInputCases : IO Unit := do
  vectorChecks
  rangeChecks
  ensure (profiles.length == 13) "a runtime-input profile is missing from the seeded input checks"
  for profile in profiles do
    checkProfile profile

end Tests.SourceSeededInputCases
