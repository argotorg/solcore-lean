import Solcore.Synthesis.Source.MutationCases
import Solcore.Synthesis.Source.ClosureCases
import Solcore.Synthesis.Source.ComptimeCases
import Solcore.Synthesis.Source.ModuleCases
import Solcore.Synthesis.Source.GenericCases
import Solcore.Synthesis.Source.CallGraphLoopCases
import Solcore.Synthesis.Source.AggregateCallGraphCases
import Solcore.Synthesis.Source.AssemblyCases
import Solcore.Synthesis.Source.AssemblyMemoryCases
import Solcore.Synthesis.Source.EnumCases
import Solcore.Synthesis.Source.TraitCases

/-! The identity filter `exclude-boundary-identity-v1` of the fourteen runtime-input
profiles whose generated functions can be identities. Over a window of
attempts it excludes exactly the functions that return every boundary input
unchanged, under its own reason and code, and keeps every other function with
all of its cases. Filtered cases record the filter, replay exactly, compose
with seeded inputs and leave their reductions unfiltered; a saved identity
cannot claim the filter. The loop profiles already exclude identities, and a
generic selection returns equal or adjacent Words for inputs 0 and 1. -/
set_option autoImplicit false

namespace Tests.SourceAcceptanceCases

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

private def errorOf {α : Type} : Except String α → Option String
  | .error error => some error
  | .ok _ => none

private structure Profile where
  name : String
  generate : Seed → Nat → Nat → Nat → Nat → InputSelection → Acceptance → Json
  replay : Json → Nat → Except String Json
  shrink : Json → Nat → Nat → Except String Json
  nodes : Nat
  /-- Boundary inputs per function. -/
  inputs : Nat
  /-- A seed whose function is a boundary identity under the profile's own filters. -/
  identity : Option Nat

private def profiles : List Profile := [
  {name := "runtime-word", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Input.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Input.replayCase, shrink := Input.shrinkCases, nodes := 32, inputs := 4, identity := some 8},
  {name := "runtime-primitives", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Primitive.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Primitive.replayCase, shrink := Primitive.shrinkCases, nodes := 96, inputs := 8,
    identity := some 8},
  {name := "runtime-assembly", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Assembly.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Assembly.replayCase, shrink := Assembly.shrinkCases, nodes := 96, inputs := 8,
    identity := some 8},
  {name := "runtime-assembly-memory", generate := fun seed nodes count attempts fuel inputs acceptance =>
      AssemblyMemory.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := AssemblyMemory.replayCase, shrink := AssemblyMemory.shrinkCases, nodes := 96, inputs := 8,
    identity := some 108},
  {name := "runtime-functions", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Solcore.Synthesis.Source.Function.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Solcore.Synthesis.Source.Function.replayCase, shrink := Solcore.Synthesis.Source.Function.shrinkCases,
    nodes := 32, inputs := 4, identity := some 12},
  {name := "runtime-mutation", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Mutation.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Mutation.replayCase, shrink := Mutation.shrinkCases, nodes := 192, inputs := 4,
    identity := some 184},
  {name := "runtime-aggregates", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Aggregate.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Aggregate.replayCase, shrink := Aggregate.shrinkCases, nodes := 256, inputs := 4,
    identity := some 3},
  {name := "runtime-closures", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Closure.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Closure.replayCase, shrink := Closure.shrinkCases, nodes := 384, inputs := 4, identity := none},
  {name := "runtime-comptime", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Comptime.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Comptime.replayCase, shrink := Comptime.shrinkCases, nodes := 384, inputs := 4,
    identity := some 60},
  {name := "runtime-modules", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Modules.generateCases seed nodes count attempts fuel .v4 inputs acceptance,
    replay := Modules.replayCase, shrink := Modules.shrinkCases, nodes := 384, inputs := 4, identity := none},
  {name := "runtime-call-graphs", generate := fun seed nodes count attempts fuel inputs acceptance =>
      CallGraph.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := CallGraph.replayCase, shrink := CallGraph.shrinkCases, nodes := 192, inputs := 8,
    identity := some 2},
  {name := "runtime-aggregate-call-graphs", generate := fun seed nodes count attempts fuel inputs acceptance =>
      AggregateCallGraph.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := AggregateCallGraph.replayCase, shrink := AggregateCallGraph.shrinkCases, nodes := 192,
    inputs := 8, identity := some 5},
  {name := "runtime-enums", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Enums.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := Enums.replayCase, shrink := Enums.shrinkCases, nodes := 2048, inputs := 8, identity := none},
  {name := "runtime-traits", generate := fun seed nodes count attempts fuel inputs acceptance =>
      Traits.generateCases seed nodes count attempts fuel inputs acceptance,
    replay := Traits.replayCase, shrink := Traits.shrinkCases, nodes := 2048, inputs := 8, identity := none}]

private def fuel : Nat := 1000000

/-- Every function of one window is returned, so the two filters compare whole. -/
private def window : Nat := 24

private def cases (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "cases")

private def excluded (corpus : Json) : IO (Array Json) :=
  get (corpus.getObjValAs? (Array Json) "excluded")

private def origin (case : Json) : IO Json := do
  get ((← get (case.getObjVal? "provenance")).getObjVal? "origin")

private def withOrigin (case : Json) (change : Json → Json) : IO Json := do
  let provenance ← get (case.getObjVal? "provenance")
  return case.setObjVal! "provenance" (provenance.setObjVal! "origin" (change (← origin case)))

private def withoutAcceptance : Json → Json
  | .obj fields => .obj (fields.erase "acceptance")
  | other => other

/-- One accepted function yields its inputs consecutively, in input order. -/
private def functions (all : Array Json) (size : Nat) : List (Array Json) :=
  (List.range (all.size / size)).map fun index => all.extract (index * size) ((index + 1) * size)

/-- The function returned each of these inputs unchanged. -/
private def isIdentity (function : Array Json) : IO Bool := do
  for case in function do
    let input ← get (case.getObjValAs? String "input")
    let result ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
    unless input == result do return false
  return true

private def reason (entry : Json) : String :=
  (entry.getObjValAs? String "reason").toOption.getD ""

private def checkWindow (profile : Profile) : IO Unit := do
  let generate := fun acceptance =>
    profile.generate (Seed.ofNat 1) profile.nodes 1024 window fuel .boundary acceptance
  let (unfiltered, filtered) := (generate .profile, generate .nonIdentity)
  let all ← cases unfiltered
  ensure (all.size % profile.inputs == 0) s!"{profile.name}: a function lost some of its boundary inputs"
  let mut kept : Array Json := #[]
  let mut identities := 0
  for function in functions all profile.inputs do
    if ← isIdentity function then identities := identities + 1 else kept := kept ++ function
  let accepted ← cases filtered
  ensure ((← accepted.mapM fun case => withOrigin case withoutAcceptance) == kept)
    s!"{profile.name}: the filter did not keep exactly the functions that change a boundary input"
  let before ← excluded unfiltered
  let after ← excluded filtered
  let identityEntries := after.filter (reason · == Acceptance.identityReason)
  ensure (identityEntries.size == identities && after.filter (reason · != Acceptance.identityReason) == before)
    s!"{profile.name}: the filter excluded something other than the boundary identities"
  for entry in identityEntries do
    ensure ((entry.getObjValAs? String "code").toOption == some "boundary-identity" &&
        (entry.getObjValAs? String "category").toOption == some "excluded")
      s!"{profile.name}: an identity exclusion lacks its own code"
  if let some seed := profile.identity then
    if seed ≤ window then
      ensure (identities > 0) s!"{profile.name}: the window holds no identity to exclude"
  for case in accepted.extract 0 (2 * profile.inputs) do
    ensure (((← origin case).getObjValAs? String "acceptance").toOption == some Acceptance.nonIdentityVersion)
      s!"{profile.name}: a filtered case does not record its filter"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a filtered case failed exact replay"
    let unlabeled ← withOrigin case withoutAcceptance
    ensure ((← get (profile.replay unlabeled fuel)) == unlabeled)
      s!"{profile.name}: a filtered case is not also a case of the profile's own filters"
    let unknown ← withOrigin case (·.setObjVal! "acceptance" (toJson "exclude-boundary-identity-v9"))
    ensure (errorOf (profile.replay unknown fuel) == some "unsupported acceptance filter")
      s!"{profile.name}: an unknown acceptance filter replayed"

/-- A function that returns every boundary input is excluded under the filter
alone, and its saved unfiltered case cannot claim the filter. -/
private def checkIdentity (profile : Profile) (seed : Nat) : IO Unit := do
  let generate := fun acceptance =>
    profile.generate (Seed.ofNat seed) profile.nodes profile.inputs 1 fuel .boundary acceptance
  let identity ← cases (generate .profile)
  ensure (identity.size == profile.inputs && (← isIdentity identity))
    s!"{profile.name}: seed {seed} is not a boundary identity of the profile's own filters"
  let filtered := generate .nonIdentity
  ensure ((← cases filtered).isEmpty && ((← excluded filtered).map reason) == #[Acceptance.identityReason])
    s!"{profile.name}: the filter did not exclude the identity of seed {seed}"
  for case in identity do
    let claimed ← withOrigin case (·.setObjVal! "acceptance" (toJson Acceptance.nonIdentityVersion))
    ensure (errorOf (profile.replay claimed fuel) == some Acceptance.identityReason)
      s!"{profile.name}: a saved identity replayed under the filter"

/-- Seeded inputs follow the boundary inputs; reductions are never filtered. -/
private def checkSeededAndReductions (profile : Profile) : IO Unit := do
  let seeded ← cases (profile.generate (Seed.ofNat 1) profile.nodes (profile.inputs + 4) 64 fuel .seeded .nonIdentity)
  ensure (seeded.size == profile.inputs + 4) s!"{profile.name}: seeded filtered generation did not complete"
  for case in seeded do
    let saved ← origin case
    ensure ((saved.getObjValAs? String "acceptance").toOption == some Acceptance.nonIdentityVersion &&
        (saved.getObjValAs? String "inputSelection").toOption == some InputSelection.seededVersion)
      s!"{profile.name}: a seeded filtered case does not record both choices"
    ensure ((← get (profile.replay case fuel)) == case) s!"{profile.name}: a seeded filtered case failed exact replay"
  let some first := seeded[0]? | throw (IO.userError s!"{profile.name}: no filtered case")
  let reduced ← cases (← get (profile.shrink first 3 fuel))
  ensure (!reduced.isEmpty) s!"{profile.name}: a filtered case has no reduction candidate"
  for candidate in reduced do
    let saved ← origin candidate
    ensure ((saved.getObjValAs? String "kind").toOption == some "reduced" &&
        (saved.getObjVal? "acceptance").toOption.isNone)
      s!"{profile.name}: a reduction carries the acceptance filter"
    ensure ((← get (profile.replay candidate fuel)) == candidate)
      s!"{profile.name}: a reduction of a filtered case failed exact replay"

private def resultWord (case : Json) : IO Nat := do
  let text ← get ((← get (case.getObjVal? "directCore")).getObjValAs? String "word")
  let some value := text.toNat? | throw (IO.userError "invalid result Word")
  return value

/-- The profiles left unchanged: every loop changes a positive-trip boundary
input, so none is an identity, and a generic function returns `f 1` or
`f 1 + 1` for input 0, so it cannot return both 0 and 1. -/
private def unchangedProfiles : IO Unit := do
  for (name, corpus, size) in [
      ("runtime-loops", Loop.generateCases (Seed.ofNat 1) 384 1024 window fuel .v4, 6),
      ("runtime-call-graph-loops", CallGraphLoop.generateCases (Seed.ofNat 1) 256 1024 (4 * window) fuel, 6)] do
    let all ← cases corpus
    ensure (all.size ≥ 4 * size) s!"{name}: too few loops to check"
    for function in functions all size do
      ensure (!(← isIdentity function)) s!"{name}: a generated loop returned every boundary input"
  let generic ← cases (Generic.generateCases (Seed.ofNat 1) 384 1024 window fuel .v4)
  ensure (generic.size ≥ 16) "runtime-generics: too few functions to check"
  for function in functions generic 4 do
    let (atZero, atOne) := (← resultWord function[0]!, ← resultWord function[1]!)
    ensure (atZero == atOne || atZero == (atOne + 1) % 2 ^ 256)
      "runtime-generics: input 0 returned neither the result of input 1 nor its successor"

private def acceptanceChecks : IO Unit := do
  ensure (Acceptance.ofVersion? Acceptance.nonIdentityVersion == some .nonIdentity &&
      Acceptance.ofVersion? "profile" == none) "acceptance filter versions changed"
  let origin := Json.mkObj [("kind", toJson "input-generated")]
  ensure ((Acceptance.ofOrigin origin).toOption == some .profile && Acceptance.record .profile origin == origin &&
      (Acceptance.ofOrigin (Acceptance.record .nonIdentity origin)).toOption == some .nonIdentity &&
      errorOf (Acceptance.ofOrigin (origin.setObjVal! "acceptance" (toJson (1 : Nat)))) ==
        some "unsupported acceptance filter")
    "acceptance filters do not round-trip through an origin"
  let inputs := [Word.zero, Word.ofNatModulo 1]
  ensure (errorOf (Acceptance.check .nonIdentity inputs inputs) == some Acceptance.identityReason &&
      errorOf (Acceptance.check .nonIdentity inputs [Word.zero, Word.zero]) == none &&
      errorOf (Acceptance.check .profile inputs inputs) == none) "the identity filter decides the wrong functions"

def testSourceAcceptanceCases : IO Unit := do
  acceptanceChecks
  ensure (profiles.length == 14) "a profile whose functions can be identities is missing"
  for profile in profiles do
    checkWindow profile
    if let some seed := profile.identity then checkIdentity profile seed
    checkSeededAndReductions profile
  unchangedProfiles

end Tests.SourceAcceptanceCases
