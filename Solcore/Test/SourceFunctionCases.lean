import Solcore.Synthesis.Source.FunctionCases

/-! Bounded acyclic-function generation, original Core execution, provenance
replay and checked shrinking. This does not assume source-printer correctness. -/
set_option autoImplicit false

namespace Tests.SourceFunctionCases
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejected {α : Type} (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def field (value : Json) (name : String) : IO Json := get (value.getObjVal? name)
private def string (value : Json) (name : String) : IO String := get (value.getObjValAs? String name)
private def natural (value : Json) (name : String) : IO Nat := get (value.getObjValAs? Nat name)
private def cases (value : Json) : IO (Array Json) := get (value.getObjValAs? (Array Json) "cases")
private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)

private def checked (helpers : List Wire.Expr) (entry : Wire.Expr) : IO CheckedWordFunctionDAG :=
  match CheckedWordFunctionDAG.ofParts? helpers entry with
  | some value => pure value
  | none => throw (IO.userError "function case fixture did not typecheck")

private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def diamond : List Wire.Expr := [
  .binary .wordXor (.var 0) (word 3),
  .letE (.apply (.var 1) (.var 0)) (.binary .wordAdd (.var 0) (.var 1)),
  .binary .wordXor (.apply (.var 1) (.var 0)) (.apply (.var 2) (.var 0))]

private def imported (helpers : List Wire.Expr) (input : Word) : IO Json := do
  get (Function.emitCase (← checked helpers entry) input (Json.mkObj [("kind", toJson "imported")]) 1000)

private def returned (value : Word) : Json := Json.mkObj [
  ("stage", toJson "execution"), ("status", toJson "returned"),
  ("word", toJson (toString value.val))]

private def originalCoreChecks : IO Unit := do
  let graph ← checked diamond entry
  ensure (graph.features.count "functionCall" == 4) "callee variables were mistaken for scalar expressions"
  let mut emitted : Option String := none
  for input in Input.boundaryInputs do
    let saved ← get (Function.emitCase graph input (Json.mkObj [("kind", toJson "imported")]) 1000)
    let zero := Word.ofNatModulo 3
    let first := input.bitXor zero
    let expected := (first.add input).bitXor first
    ensure ((← field saved "directCore") == returned expected) "diamond calls changed original Core meaning"
    let source ← string saved "source"
    if let some previous := emitted then ensure (previous == source) "source text depends on the input"
    emitted := some source
    let admitted ← get (Function.caseProgram saved)
    ensure (admitted.program.check && admitted.function.helpers.length == 3)
      "applied diamond escaped full checker/shape admission"
    ensure ((← get (Function.replayCase saved 1000)) == saved) "imported DAG did not replay exactly"
    let forged := saved.setObjVal! "directCore" (returned (Word.ofNatModulo 777))
    ensure ((← get (Function.replayCase forged 1000)) == saved) "stored expected result was trusted"
    let low ← get (Function.replayCase saved 0)
    ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
      "original Core fuel exhaustion was treated as a value"
  let constant ← checked [word 17] (word 3)
  let saved ← get (Function.emitCase constant Word.maximum
    (Json.mkObj [("kind", toJson "imported")]) 1000)
  ensure ((← field saved "directCore") == returned (Word.ofNatModulo 3))
    "constant reduced/imported DAG must remain admissible"
  rejected (Function.inputSensitive constant 1000) "constant generated graph passed the input filter"
  let unsupported ← checked [.binary .wordDiv (.var 0) (word 2)] entry
  rejected (Function.emitCase unsupported Word.zero (Json.mkObj [("kind", toJson "imported")]) 1000)
    "unsupported scalar operation silently entered the function emitter"
  let large := (List.range 254).foldl (fun body _ => .binary .wordAdd body (word 0))
    (.var 0 : Wire.Expr)
  let oversized ← checked [large] entry
  rejected (Function.emitCase oversized Word.zero (Json.mkObj [("kind", toJson "imported")]) 1000)
    "oversized applied DAG escaped the 512-node case limit"

private def generationChecks : IO Json := do
  let mut last := Json.null
  for seed in List.range 3 do
    let count := seed + 1
    let budget := 9 * count + 6
    let corpus := Function.generateCases (Seed.ofNat seed) budget 4 1 1000
    ensure (corpus == Function.generateCases (Seed.ofNat seed) budget 4 1 1000)
      "helper generation is not deterministic"
    ensure ((← string corpus "status") == "complete" && (← natural corpus "attempted") == 1)
      "minimum valid helper budget did not emit its fixed function"
    let rows ← cases corpus
    ensure (rows.size == 4) "one function did not emit its four boundary cases"
    for index in List.range 4 do
      let saved := rows[index]!
      let admitted ← get (Function.caseProgram saved)
      ensure (admitted.function.helpers.length == count && admitted.program.check &&
        Wire.programNodes admitted.program ≤ budget) "generation violated helper count/type/node budget"
      ensure (some admitted.input == Input.boundaryInputs[index]?) "boundary ordering changed"
      ensure ((← field saved "directCore") == returned (admitted.input.mul (Word.ofNatModulo count)))
        "generated entry did not execute its complete helper chain"
      ensure ((← get (Function.replayCase saved 1000)) == saved) "generated DAG replay differs"
      let low ← get (Function.replayCase saved 0)
      ensure ((← string (← field low "directCore") "status") == "out-of-fuel")
        "replay failed to separate validation fuel from fresh observation fuel"
      last := saved
    let tooSmall := Function.generateCases (Seed.ofNat seed) (budget - 1) 1 1 1000
    ensure ((← cases tooSmall).isEmpty && (← string tooSmall "status") == "generation-exhausted")
      "small budget silently changed the helper count"
  let varied := Function.generateCases (Seed.ofNat 0) 48 12 256 1000
  ensure ((← cases varied).size == 12 && (← natural varied "attempted") ≤ 256)
    "bounded mixed helper generation failed"
  for saved in ← cases varied do
    let admitted ← get (Function.caseProgram saved)
    ensure (Wire.programNodes admitted.program ≤ 48) "mixed helper generation exceeded requested budget"
    ensure ((← get (Function.replayCase saved 1000)) == saved) "mixed helper provenance did not replay"
  let low := Function.generateCases (Seed.ofNat 0) 15 1 1 0
  let excluded ← get (low.getObjValAs? (Array Json) "excluded")
  ensure ((← string excluded[0]! "category") == "inconclusive-resource" &&
    (← string excluded[0]! "code") == "boundary-out-of-fuel") "generation fuel was a semantic exclusion"
  ensure ((← cases (Function.generateCases (Seed.ofNat 0) 15 3 1 1000)).size == 3)
    "count did not truncate the final boundary group"
  ensure ((← string (Function.generateCases (Seed.ofNat 0) 15 5 1 1000) "status") == "generation-exhausted")
    "function attempts were confused with input case count"
  ensure ((← natural (Function.generateCases (Seed.ofNat 0) 48 0 100 1000) "attempted") == 0)
    "zero case count consumed generation attempts"
  ensure ((← cases (Function.generateCases (Seed.ofNat 0) 48 1 0 1000)).isEmpty)
    "zero attempt budget was ignored"
  let wrapped := Function.generateCases (Seed.ofNat (2 ^ 64 - 2)) 33 4 1 1000
  for saved in ← cases wrapped do
    ensure ((← get (Function.replayCase saved 1000)) == saved) "uint64 helper seed wrap did not replay"
  ensure ((← cases wrapped).size == 4) "uint64 seed-wrap fixture did not emit"
  return last

private def tamperingChecks (saved : Json) : IO Unit := do
  let provenance ← field saved "provenance"
  let origin ← field provenance "origin"
  let withOrigin := fun replacement => saved.setObjVal! "provenance" (provenance.setObjVal! "origin" replacement)
  for name in ["generatorVersion", "profileVersion", "functionVersion", "abstractionVersion",
      "emitterVersion", "wrapperVersion"] do
    rejected (Function.replayCase (saved.setObjVal! "provenance"
      (provenance.setObjVal! name (toJson "forged"))) 1000) "tampered version accepted"
  for (name, value) in [("seed", toJson "02"), ("finalSeed", toJson "0"),
      ("maxProgramNodes", toJson (513 : Nat)), ("helperCount", toJson (0 : Nat)),
      ("inputIndex", toJson (999 : Nat)), ("validationFuel", toJson (10000001 : Nat)),
      ("helpers", Json.arr #[]), ("kind", toJson "unknown")] do
    rejected (Function.replayCase (withOrigin (origin.setObjVal! name value)) 1000)
      s!"tampered {name} provenance accepted"
  let metadata ← get (origin.getObjValAs? (Array Json) "helpers")
  let first := metadata[0]!
  for (name, value) in [("seed", toJson "0"), ("finalSeed", toJson "0"),
      ("literalIndex", toJson (99 : Nat)), ("maxProgramNodes", toJson (99 : Nat))] do
    rejected (Function.replayCase (withOrigin (origin.setObjVal! "helpers"
      (.arr (metadata.set! 0 (first.setObjVal! name value))))) 1000) "tampered helper provenance accepted"
  rejected (Function.replayCase (saved.setObjVal! "source" (toJson "stale")) 1000) "stale source accepted"
  rejected (Function.replayCase (saved.setObjVal! "input" (toJson "0")) 1000) "input/program mismatch accepted"
  let contract ← field saved "contract"
  rejected (Function.replayCase (saved.setObjVal! "contract"
    (contract.setObjVal! "calldata" (toJson "0xa444f5e9"))) 1000) "incorrect ABI argument accepted"
  rejected (Function.replayCase (saved.setObjVal! "provenance"
    (provenance.setObjVal! "features" (toJson ["functionCall"]))) 1000) "incorrect features accepted"
  for helpers in [[], [.apply (.var 1) (.var 0)], [.var 0, .apply (.var 2) (.var 0)],
      [.var 0, .var 0, .var 0, .var 0]] do
    rejected (Function.checkedFunction (Wire.encodeProgram (functionDAGProgram helpers entry)))
      "empty/recursive/forward-reference/too-many-helper DAG accepted"
  let (constant, constantOrigin) ← get (Function.generatedFunction (Seed.ofNat 83) 48)
  let forgedOrigin := (constantOrigin.setObjVal! "inputIndex" (toJson (0 : Nat))).setObjVal!
    "validationFuel" (toJson (1000 : Nat))
  let forged ← get (Function.emitCase constant Word.zero forgedOrigin 1000)
  rejected (Function.replayCase forged 1000)
    "constant-on-boundaries generated graph escaped sensitivity revalidation"

private def shrinkChecks : IO Unit := do
  let saved ← imported diamond Word.maximum
  let original ← get (Function.caseProgram saved)
  let shrunk ← get (Function.shrinkCases saved 1000 1000)
  let rows ← cases shrunk
  ensure (!rows.isEmpty && shrunk == (← get (Function.shrinkCases saved 1000 1000)))
    "function shrinking was empty or nondeterministic"
  let mut seen : List String := []
  let mut inputReduced := false
  let mut bodyReduced := false
  for row in rows do
    let candidate ← get (Function.caseProgram row)
    ensure (candidate.program.check && candidate.function.helpers.length == original.function.helpers.length &&
      Wire.programNodes candidate.program ≤ 512) "shrink changed helper count or broke checker/shape"
    ensure ((complexity candidate.program.body).isStrictlySmaller (complexity original.program.body))
      "function shrink did not strictly reduce applied Core complexity"
    let key := (Wire.encodeProgram candidate.program).compress
    ensure (!seen.contains key) "function shrink duplicated a candidate"
    seen := key :: seen
    ensure ((← get (Function.replayCase row 1000)) == row) "function shrink failed replay"
    let emitted ← get ((Function.emit candidate.function).mapError reprStr)
    ensure ((← string row "source") == emitted.source) "function shrink retained stale source"
    inputReduced := inputReduced || candidate.input != original.input
    bodyReduced := bodyReduced || Wire.encodeProgram candidate.function.program !=
      Wire.encodeProgram original.function.program
  ensure (inputReduced && bodyReduced) "function shrink omitted body/input reductions"
  ensure ((← cases (← get (Function.shrinkCases saved 2 1000))) == rows.extract 0 2)
    "function shrink limit changed ordering"
  ensure ((← cases (← get (Function.shrinkCases saved 0 1000))).isEmpty) "zero shrink limit ignored"
  rejected (Function.shrinkCases (saved.setObjVal! "source" (toJson "stale")) 10 1000)
    "function shrink accepted stale source"

def testSourceFunctionCases : IO Unit := do
  originalCoreChecks
  let generated ← generationChecks
  tamperingChecks generated
  shrinkChecks

end Tests.SourceFunctionCases
