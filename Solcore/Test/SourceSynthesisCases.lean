import Solcore.Synthesis.Source.Cases
import Solcore.Test.SourceSynthesisEmitter

/-! Replay, bounded generation and checked reduction regressions. Saved
observations are deliberately untrusted; these checks do not prove the printer
or either compiler preserves the original Core computation. -/
set_option autoImplicit false

namespace Tests.SourceSynthesisCases

open Lean
open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} (result : Except String α)
    (expected : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"tampered case accepted: {expected}")
  | .error error => ensure (error == expected) s!"unexpected rejection: {error}; expected {expected}"

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def checked (body : Wire.Expr) : IO CheckedWordProgram :=
  match CheckedWordProgram.ofProgram? (SourceSynthesisEmitter.fixtureProgram body) with
  | some value => pure value
  | none => throw (IO.userError "source case regression fixture did not typecheck")

private def imported (body : Wire.Expr) (fuel : Nat := 1000) : IO Json := do
  get ((emitCase (← checked body) (Json.mkObj [("kind", toJson "imported")]) fuel).mapError reprStr)

private def arrayField (value : Json) (field : String) : IO (Array Json) :=
  get (value.getObjValAs? (Array Json) field)

private def stringField (value : Json) (field : String) : IO String :=
  get (value.getObjValAs? String field)

private def natField (value : Json) (field : String) : IO Nat :=
  get (value.getObjValAs? Nat field)

private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)

private def returned (value : Nat) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value))]

private def outOfFuel : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "out-of-fuel")]

private def generationChecks : IO Json := do
  let corpus := generateCases (Seed.ofNat 0) 24 12 64 1000
  ensure (corpus == generateCases (Seed.ofNat 0) 24 12 64 1000)
    "bounded source corpus generation is not deterministic"
  ensure ((← stringField corpus "schema") == corpusSchema) "incorrect corpus schema"
  ensure ((← stringField corpus "status") == "complete") "bounded corpus did not complete"
  let cases ← arrayField corpus "cases"
  let excluded ← arrayField corpus "excluded"
  let attempted ← natField corpus "attempted"
  ensure (cases.size == 12 && attempted ≤ 64 && attempted == cases.size + excluded.size)
    "generation exceeded its limits or lost an attempt"
  ensure (!excluded.isEmpty) "corpus no longer exercises explicit unsupported-operation exclusions"
  for saved in cases do
    let admitted ← get (caseProgram saved)
    ensure (admitted.program.check && Wire.programNodes admitted.program ≤ 24 &&
      supported admitted.program.body) "generated case escaped its checked supported node budget"
    ensure ((← get (replayCase saved 1000)) == saved) "generated case failed exact replay"
  for excludedCase in excluded do
    ensure ((← stringField excludedCase "stage") == "emission")
      "valid-budget exclusion was not an explicit emission failure"
    let seedText ← stringField excludedCase "seed"
    let some seed := seedText.toNat? | throw (IO.userError "excluded seed is not a natural number")
    let generated ← get ((generate {seed := Seed.ofNat seed, maxProgramNodes := 24}).mapError reprStr)
    match emit generated.checkedProgram with
    | .ok _ => throw (IO.userError "an emitter-supported generated case was excluded")
    | .error error =>
      ensure ((← stringField excludedCase "reason") == reprStr error)
        "an excluded case lost the explicit emitter error"
  let exhausted := generateCases (Seed.ofNat 0) 3 3 2 1000
  ensure ((← stringField exhausted "status") == "generation-exhausted" &&
    (← natField exhausted "attempted") == 2 && (← arrayField exhausted "cases").size == 2)
    "attempt exhaustion was silently reported as a complete corpus"
  let invalidBudget := generateCases (Seed.ofNat 0) 2 1 3 1000
  ensure ((← stringField invalidBudget "status") == "generation-exhausted" &&
    (← arrayField invalidBudget "cases").isEmpty &&
    (← natField invalidBudget "attempted") == 3) "invalid generation budgets escaped the attempt bound"
  for exclusion in ← arrayField invalidBudget "excluded" do
    ensure ((← stringField exclusion "stage") == "generation" &&
      (← stringField exclusion "reason") == reprStr GenerationError.budgetTooSmall)
      "generation failures were not recorded explicitly"
  let noAttempts := generateCases (Seed.ofNat 0) 24 1 0 1000
  ensure ((← stringField noAttempts "status") == "generation-exhausted" &&
    (← natField noAttempts "attempted") == 0) "zero attempt limit was ignored"
  let noCases := generateCases (Seed.ofNat 0) 24 0 64 1000
  ensure ((← stringField noCases "status") == "complete" &&
    (← natField noCases "attempted") == 0) "empty corpus unnecessarily consumed attempts"
  let unsupported ← checked (.binary .wordDiv (word 1) (word 0))
  match emitCase unsupported (Json.mkObj [("kind", toJson "imported")]) 1000 with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "case construction did not explicitly reject unsupported division")
  pure corpus

private def observationChecks : IO Unit := do
  for (body, expected) in [
      (.binary .wordAdd (.word Word.maximum) (word 1), 0),
      (.binary .wordSub (word 0) (word 1), Word.maximum.val),
      (.ifE (.binary .wordGt (word (2 ^ 255)) (word 1)) (word 17) (word 19), 17),
      (SourceSynthesisEmitter.scopedBranch true, 14),
      (SourceSynthesisEmitter.scopedBranch false, 29)] do
    let admitted ← checked body
    ensure (observe admitted 1000 == returned expected) "original Core observation changed"
    ensure (observe admitted 0 == outOfFuel) "zero fuel was confused with a result or language fault"
  let saved ← imported (word 7)
  let forged := saved.setObjVal! "directCore" (returned 999)
  let replayed ← get (replayCase forged 1000)
  ensure (replayed == saved) "replay trusted a forged stored direct Core observation"
  let suspended ← get (replayCase forged 0)
  ensure ((← field suspended "directCore") == outOfFuel &&
    (← natField suspended "executionFuel") == 0) "replay ignored its new fuel budget"

private def tamperingChecks (corpus : Json) : IO Unit := do
  let saved ← imported (SourceSynthesisEmitter.scopedBranch false)
  rejected (replayCase (saved.setObjVal! "schema" (toJson "unknown")) 1000)
    "unsupported semantic case schema"
  rejected (replayCase (saved.setObjVal! "source" (toJson "contract Forged {}")) 1000)
    "saved source differs from emission of the original Core program"
  let provenance ← field saved "provenance"
  for (version, expected) in [
      ("generatorVersion", "generator version changed"),
      ("emitterVersion", "emitter version changed"),
      ("wrapperVersion", "wrapper version changed")] do
    rejected (replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! version (toJson "forged"))) 1000) expected
  rejected (replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ([] : List String)))) 1000)
    "saved features differ from the original Core program"
  let contract ← field saved "contract"
  for (name, value) in [("name", toJson "Other"), ("method", toJson "other"),
      ("signature", toJson "other()"), ("calldata", toJson "0x00000000"),
      ("constructorCalldata", toJson "0x01"), ("deployPath", toJson ["OtherDeploy"]),
      ("runtimePath", toJson ["OtherDeploy", "Other"])] do
    rejected (replayCase (saved.setObjVal! "contract" (contract.setObjVal! name value)) 1000)
      "saved contract metadata differs from the fixed wrapper"
  let generatedCases ← arrayField corpus "cases"
  let some generated := generatedCases[0]? | throw (IO.userError "generated replay fixture missing")
  let generatedProvenance ← field generated "provenance"
  let origin ← field generatedProvenance "origin"
  let withOrigin := fun replacement => generated.setObjVal! "provenance"
    (generatedProvenance.setObjVal! "origin" replacement)
  rejected (replayCase (withOrigin (origin.setObjVal! "seed" (toJson "00"))) 1000)
    "noncanonical saved seed"
  rejected (replayCase (withOrigin (origin.setObjVal! "seed" (toJson (toString (2 ^ 64 : Nat))))) 1000)
    "noncanonical saved seed"
  rejected (replayCase (withOrigin (origin.setObjVal! "finalSeed" (toJson "forged"))) 1000)
    "saved final seed differs from generation"
  rejected (replayCase (withOrigin (origin.setObjVal! "maxProgramNodes" (toJson (513 : Nat)))) 1000)
    "saved generation budget exceeds limit"
  let originalProgram ← field generated "program"
  let mut checkedDifferentSeed := false
  for other in generatedCases do
    if !checkedDifferentSeed && (← field other "program") != originalProgram then
      let otherOrigin ← field (← field other "provenance") "origin"
      rejected (replayCase (withOrigin otherOrigin) 1000)
        "saved program differs from its generation seed"
      checkedDifferentSeed := true
  ensure checkedDifferentSeed "corpus has no distinct generated seed for provenance tampering"

private def shrinkChecks : IO Unit := do
  let original ← imported (SourceSynthesisEmitter.scopedBranch true)
  let admitted ← get (caseProgram original)
  let result ← get (shrinkCases original 100 1000)
  ensure (result == (← get (shrinkCases original 100 1000))) "source case shrinking is nondeterministic"
  let candidates ← arrayField result "cases"
  let checkedCandidates := shrink admitted
  ensure (!candidates.isEmpty && candidates.size == checkedCandidates.length)
    "source reducer lost checked Core shrink candidates"
  for candidate in candidates do
    let reduced ← get (caseProgram candidate)
    ensure (reduced.program.check && accepts .word reduced.program.body && supported reduced.program.body)
      "source reduction broke typing, closure or emitter support"
    ensure ((complexity reduced.program.body).isStrictlySmaller (complexity admitted.program.body))
      "source reduction did not strictly decrease the checked Core measure"
    let emitted ← get ((emit reduced).mapError reprStr)
    ensure ((← stringField candidate "source") == emitted.source)
      "source reduction reused stale source text"
    let origin ← field (← field candidate "provenance") "origin"
    ensure ((← stringField origin "kind") == "reduced" &&
      (← field origin "parentProgram") == Wire.encodeProgram admitted.program)
      "source reduction lost its parent provenance"
    ensure ((← get (replayCase candidate 1000)) == candidate) "reduced source case failed replay"
  let limited ← arrayField (← get (shrinkCases original 2 1000)) "cases"
  ensure (limited == candidates.extract 0 2) "source shrink limit changed candidate ordering"
  ensure ((← arrayField (← get (shrinkCases original 0 1000)) "cases").isEmpty)
    "zero shrink limit was ignored"
  rejected (shrinkCases (original.setObjVal! "source" (toJson "forged")) 10 1000)
    "saved source differs from emission of the original Core program"

def testSourceSynthesisCases : IO Unit := do
  let corpus ← generationChecks
  observationChecks
  tamperingChecks corpus
  shrinkChecks

end Tests.SourceSynthesisCases
