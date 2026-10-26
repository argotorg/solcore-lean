import Solcore.Synthesis.Source.PrimitiveCases

/-! Validate the committed primitive corpus against actual checked Core
execution. Expected Words are fixed boundary goldens, never compiler output.
This module does not compile Rust or execute an EVM. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveCorpus

open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def strings (value : Json) (key : String) : Except String (List String) := do
  let entries ← value.getObjValAs? (List String) key
  require (entries.eraseDups == entries) (key ++ " contains duplicates")
  return entries

private def sameMembers (left right : List String) : Bool :=
  left.all right.contains && right.all left.contains

private def versions : List (String × String) := [
  ("profileVersion", Primitive.profileVersion), ("functionVersion", wordFunctionVersion),
  ("abstractionVersion", abstractionVersion), ("generatorVersion", Primitive.generatorVersion),
  ("baseGeneratorVersion", Solcore.Synthesis.Core.generatorVersion), ("boundaryVersion", Primitive.boundaryVersion),
  ("emitterVersion", Primitive.emitterVersion), ("wrapperVersion", Primitive.wrapperVersion)]

/-- Materialize and replay every original function application in one bounded
Core run, before any shared case-tool executable needs to be rebuilt. -/
def validateManifest (manifest : Json) (fuel : Nat := 2000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-corpus-manifest.v1" &&
    (← string manifest "profile") == "runtime-primitives" &&
    (← string manifest "coverageKind") == "core-ast-features") "unexpected primitive manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("primitive manifest changed " ++ key)
  let requiredFeatures ← strings manifest "requiredFeatures"
  require (sameMembers requiredFeatures (Feature.catalog.toList.map featureName))
    "primitive corpus must require every scalar AST feature"
  let requiredInputs ← strings manifest "requiredInputs"
  require (sameMembers requiredInputs (Primitive.boundaryInputs.map fun value => toString value.val))
    "primitive corpus must require all eight boundary inputs"
  let requiredLiterals ← strings manifest "requiredWordLiterals"
  let entries ← manifest.getObjValAs? (Array Json) "cases"
  require (0 < entries.size && entries.size ≤ 128) "primitive corpus must contain 1..128 cases"
  let mut identifiers : List String := []
  let mut inputs : List String := []
  let mut featureUnion : List String := []
  let mut literalUnion : List String := []
  let mut sources : List (String × String) := []
  let mut reductions := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifier.isEmpty && identifier.length ≤ 80 && !identifiers.contains identifier)
      "primitive case ID is empty, duplicated or too long"
    identifiers := identifiers ++ [identifier]
    let original ← entry.getObjVal? "program"
    let function ← Primitive.checkedFunction original
    require (Wire.encodeProgram function.program == original) (identifier ++ ": noncanonical function")
    let input ← Primitive.inputWord (← string entry "input")
    let expected ← Primitive.inputWord (← string entry "expectedCore")
    let expectedFeatures ← strings entry "expectedFeatures"
    let actualFeatures := (features function.body).map featureName
    require (sameMembers expectedFeatures actualFeatures && actualFeatures.contains "local")
      (identifier ++ ": expected features differ or original function lacks runtime locals")
    let origin := Json.mkObj [("kind", toJson "imported")]
    let saved ← Primitive.emitCase function input origin fuel
    require (saved == (← Primitive.emitCase function input origin fuel)) (identifier ++ ": nondeterministic emission")
    require ((← Primitive.replayCase saved fuel) == saved) (identifier ++ ": native replay differs")
    let admitted ← Primitive.caseProgram saved
    require admitted.program.check (identifier ++ ": original Core application failed its checker")
    let actual ← saved.getObjVal? "directCore"
    require ((← string actual "status") == "returned" && (← string actual "word") == toString expected.val)
      (identifier ++ ": actual Core result differs from its independent boundary golden")
    let forged := saved.setObjVal! "directCore" (Json.mkObj [("status", toJson "forged")])
    require ((← Primitive.replayCase forged fuel) == saved) (identifier ++ ": stored observation became an oracle")
    let source ← string saved "source"
    let key := original.compress
    if let some (_, previous) := sources.find? (fun item => item.1 == key) then
      require (source == previous) (identifier ++ ": emitted source depends on runtime input")
    else sources := sources ++ [(key, source)]
    let candidates ← Primitive.shrinkCases saved 4 fuel
    for reduced in (← candidates.getObjValAs? (Array Json) "cases") do
      let candidate ← Primitive.caseProgram reduced
      require (candidate.program.check &&
        (complexity candidate.program.body).isStrictlySmaller (complexity admitted.program.body))
        (identifier ++ ": shrink is untyped or not strictly smaller")
      require ((← Primitive.replayCase reduced fuel) == reduced) (identifier ++ ": reduced case failed replay")
      reductions := reductions + 1
    inputs := (inputs ++ [toString input.val]).eraseDups
    featureUnion := (featureUnion ++ actualFeatures).eraseDups
    literalUnion := (literalUnion ++ (wordLiterals function.body).map (fun value => toString value.val)).eraseDups
  require (requiredFeatures.all featureUnion.contains) "native-completed cases missed required AST features"
  require (requiredInputs.all inputs.contains) "native-completed cases missed required runtime inputs"
  require (requiredLiterals.all literalUnion.contains) "native-completed cases missed required Word literals"
  return Json.mkObj [
    ("status", toJson "complete"), ("cases", toJson entries.size), ("functions", toJson sources.length),
    ("features", toJson featureUnion.length), ("inputs", toJson inputs.length), ("shrinks", toJson reductions),
    ("nativeCoreExecuted", toJson true), ("rustExecuted", toJson false), ("evmExecuted", toJson false)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid primitive corpus unexpectedly passed")

def testSourcePrimitiveCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-primitive-corpus.json"))
  let summary ← checked (validateManifest manifest)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first primitive case")
  let expected ← checked (Primitive.inputWord (← checked (string first "expectedCore")))
  let incorrect := first.setObjVal! "expectedCore" (toJson (toString ((expected.val + 1) % (2 ^ 256))))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.set! 0 incorrect))))
  rejects (validateManifest (manifest.setObjVal! "profile" (toJson "runtime-word")))
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr #[])))
  rejects (validateManifest (manifest.setObjVal! "requiredInputs" (toJson ([] : List String))))
  rejects (validateManifest (manifest.setObjVal! "requiredFeatures" (toJson ([] : List String))))
  rejects (validateManifest manifest 0)
  IO.println summary.compress

end Tests.SourcePrimitiveCorpus
