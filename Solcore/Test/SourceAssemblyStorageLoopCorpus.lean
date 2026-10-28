import Solcore.Synthesis.Source.AssemblyStorageLoopCases

/-! The fixed inline Yul storage-loop corpus is the storage-loop corpus in the
three forms: its generated seeds stay generated, its imported entries take
`split`, `carried` and `pipelined` in turn, in corpus order, and the entries
`seven-carried` and `seven-counts` also run in the other two forms. The
manifest must be exactly that construction, with the storage-loop corpus's
requirements and the form requirements. Every entry must replay, and its
actual original Core history must equal the expected history, which is the
storage-loop corpus's, since the Core reference is unchanged. Each form must
cover the iteration counts zero, one and seven and both carries.
Source/Rust/EVM agreement is a separate external validation. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopCorpus
open Lean Solcore.Core Solcore.Synthesis.Core Solcore.Synthesis.Source
open Solcore.Synthesis.Source.AssemblyStorage (Form)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def string (value : Json) (key : String) : Except String String :=
  value.getObjValAs? String key

private def versions : List (String × String) := [
  ("generatorVersion", generatorVersion), ("profileVersion", AssemblyStorageLoop.profileVersion),
  ("loopProfileVersion", StorageLoop.profileVersion),
  ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version),
  ("templateVersion", StorageLoop.templateVersion), ("stepProfileVersion", Aggregate.profileVersion),
  ("stepFunctionVersion", Aggregates.version), ("stepTemplateVersion", Aggregate.templateVersion),
  ("emitterVersion", AssemblyStorageLoop.emitterVersion), ("wrapperVersion", AssemblyStorageLoop.wrapperVersion)]

/-- The entries that run in every form. -/
private def everyForm : List String := ["seven-carried", "seven-counts"]

private def carryNames : List String := ["iteration", "rollback"]

/-- An imported storage-loop entry in a form. -/
private def inForm (entry : Json) (form : Form) : Except String Json := do
  let plan ← entry.getObjVal? "storageLoopPlan"
  return (entry.setObjVal! "id" (toJson ((← string entry "id") ++ "-" ++ form.name))).setObjVal! "storageLoopPlan"
    ((plan.setObjVal! "schema" (toJson AssemblyStorageLoop.planSchema)).setObjVal! "form" (toJson form.name))

/-- The corpus the definitions build from the storage-loop corpus. -/
def construction (parent : Json) : Except String (List Json) := do
  let mut turn := 0
  let mut result : List Json := []
  for entry in ← parent.getObjValAs? (List Json) "cases" do
    if (entry.getObjVal? "generation").isOk then
      result := result ++ [entry]
    else
      let form := Form.all.getD (turn % 3) .split
      turn := turn + 1
      result := result ++ [← inForm entry form]
      if everyForm.contains (← string entry "id") then
        for other in Form.all do
          if other != form then result := result ++ [← inForm entry other]
  return result

/-- Imported entries are emitted from their saved plan and sequence; generated
entries are regenerated from their seed. Both are checked by full replay. -/
private def entryCase (entry : Json) (fuel : Nat) : Except String Json := do
  if let .ok request := entry.getObjVal? "generation" then
    let some seed := (← request.getObjValAs? String "seed").toNat? | throw "invalid generation seed"
    let corpus := AssemblyStorageLoop.generateCases (Seed.ofNat seed) (← request.getObjValAs? Nat "maxProgramNodes") 1 1 fuel
    require ((← string corpus "status") == "complete") "generated entry was excluded"
    let some saved := (← corpus.getObjValAs? (Array Json) "cases")[0]? | throw "generated entry has no case"
    return saved
  let (plan, form) ← AssemblyStorageLoop.checkedPlan (← entry.getObjVal? "storageLoopPlan")
  let loop ← StorageLoop.checkedScenario plan (← StorageLoop.decodeTransactions plan.mask (← entry.getObjVal? "transactions"))
  AssemblyStorageLoop.emitCase ⟨loop, form⟩ (Json.mkObj [("kind", toJson "imported")]) fuel

/-- The carries of one scenario, as the storage-loop corpus defines them. -/
private def carries (trips : List Nat) (statuses : List String) : List String :=
  (if trips.any (· ≥ 2) then ["iteration"] else []) ++
  (if (trips.zip statuses).any (fun (count, status) => count ≥ 1 && status == "reverted") then ["rollback"] else [])

def validateManifest (manifest parent : Json) (fuel : Nat := 1000000) : Except String Json := do
  require ((← string manifest "schema") == "solcore-lean.semantic-storage-corpus-manifest.v1" &&
    (← string manifest "profile") == "stateful-assembly-storage-loops" &&
    (← string manifest "coverageKind") == "step-core-ast-features") "unexpected inline Yul storage-loop manifest scope"
  for (key, expected) in versions do
    require ((← string manifest key) == expected) ("inline Yul storage-loop manifest changed " ++ key)
  require ((← string parent "profile") == "stateful-storage-loops") "the parent corpus is not the storage-loop corpus"
  -- The storage-loop corpus's requirements carry over unchanged.
  for key in ["requiredFeatures", "requiredInputs", "requiredMasks", "requiredIterationCounts", "requiredCarriedSlots",
      "requiredIterationCarries", "requiredHelperCounts", "requiredTransactionCounts", "requiredOutcomes",
      "requiredCompletionPatterns", "generationRecipeRequirements", "coverageKind", "generatorVersion"] do
    require ((← manifest.getObjVal? key) == (← parent.getObjVal? key)) ("inline Yul storage-loop manifest changed " ++ key)
  require ((← manifest.getObjValAs? (List String) "requiredForms") == Form.all.map Form.name &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations") ==
      (Form.all.flatMap fun form => [0, 1, 7].map fun count => form.name ++ ":" ++ toString count) &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries") ==
      (Form.all.flatMap fun form => carryNames.map fun carry => form.name ++ ":" ++ carry))
    "inline Yul storage-loop corpus must require every form with iterations 0, 1 and 7 and both carries"
  let entries ← manifest.getObjValAs? (List Json) "cases"
  require (entries == (← construction parent)) "inline Yul storage-loop corpus differs from its construction"
  let mut identifiers : List String := []
  let mut forms : List String := []
  let mut formIterations : List String := []
  let mut formCarries : List String := []
  let mut transactionTotal := 0
  for entry in entries do
    let identifier ← string entry "id"
    require (!identifiers.contains identifier) ("duplicate inline Yul storage-loop corpus id " ++ identifier)
    identifiers := identifier :: identifiers
    let saved ← entryCase entry fuel
    require ((← AssemblyStorageLoop.replayCase saved fuel) == saved)
      ("inline Yul storage-loop corpus entry did not replay: " ++ identifier)
    let scenario ← AssemblyStorageLoop.caseProgram saved
    if !(entry.getObjVal? "generation").isOk then
      require ((← saved.getObjVal? "storageLoopPlan") == (← entry.getObjVal? "storageLoopPlan") &&
        (← saved.getObjVal? "transactions") == (← entry.getObjVal? "transactions"))
        ("imported inline Yul storage-loop entry is not canonical: " ++ identifier)
    let caseFeatures := (← (← saved.getObjVal? "provenance").getObjValAs? (List String) "features").eraseDups
    let expectedFeatures ← entry.getObjValAs? (List String) "expectedFeatures"
    require (expectedFeatures.all caseFeatures.contains && caseFeatures.all expectedFeatures.contains)
      ("inline Yul storage-loop corpus features changed: " ++ identifier)
    let history := AssemblyStorageLoop.observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
    require ((← string history "status") == "complete") ("inline Yul storage-loop corpus history incomplete: " ++ identifier)
    let observed ← history.getObjValAs? (List Json) "transactions"
    let expected ← entry.getObjValAs? (List Json) "expectedHistory"
    require (observed.length == expected.length) ("inline Yul storage-loop expected history length changed: " ++ identifier)
    let mut statuses : List String := []
    for (row, golden) in observed.zip expected do
      let actual := Json.mkObj [("id", ← row.getObjVal? "id"), ("status", ← row.getObjVal? "status"),
        ("output", ← row.getObjVal? "output"), ("committedStorage", ← row.getObjVal? "committedStorage")]
      require (actual == golden)
        ("original Core differs from the expected storage-loop history: " ++ identifier ++ " " ++ actual.compress)
      statuses := statuses ++ [← string row "status"]
    let trips := scenario.transactions.map fun tx =>
      Solcore.Synthesis.Stateful.StorageLoopExecution.iterations scenario.plan.mask tx.input
    let form := scenario.form.name
    transactionTotal := transactionTotal + observed.length
    forms := (forms ++ [form]).eraseDups
    formIterations := (formIterations ++ trips.map fun count => form ++ ":" ++ toString count).eraseDups
    formCarries := (formCarries ++ (carries trips statuses).map (form ++ ":" ++ ·)).eraseDups
  require ((← manifest.getObjValAs? (List String) "requiredForms").all forms.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormIterations").all formIterations.contains &&
    (← manifest.getObjValAs? (List String) "requiredFormCarries").all formCarries.contains)
    "inline Yul storage-loop corpus misses a form, a form's iteration count or a form's carry"
  return Json.mkObj [("profile", toJson "stateful-assembly-storage-loops"), ("scenarios", toJson entries.length),
    ("transactions", toJson transactionTotal), ("forms", toJson forms),
    ("formIterations", toJson formIterations), ("formCarries", toJson formCarries)]

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejects {α : Type} (result : Except String α) (reason : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError ("invalid inline Yul storage-loop corpus unexpectedly passed: " ++ reason))

def testSourceAssemblyStorageLoopCorpus : IO Unit := do
  let manifest ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-assembly-storage-loop-corpus.json"))
  let parent ← checked (Json.parse (← IO.FS.readFile "scripts/semantic-storage-loop-corpus.json"))
  let summary ← checked (validateManifest manifest parent)
  let entries ← checked (manifest.getObjValAs? (Array Json) "cases")
  let some first := entries[0]? | throw (IO.userError "missing first inline Yul storage-loop case")
  let replace := fun (original changed : Json) => manifest.setObjVal! "cases"
    (.arr (entries.map fun entry => if entry == original then changed else entry))
  let history ← checked (first.getObjValAs? (Array Json) "expectedHistory")
  let row := history[0]!
  let withRow := fun (changed : Json) => replace first (first.setObjVal! "expectedHistory" (.arr (history.set! 0 changed)))
  -- An output, a slot and a missing row are checked, and so is the construction.
  rejects (validateManifest (withRow (row.setObjVal! "output" (toJson ("0x" ++ String.ofList (List.replicate 64 'f')))))
    parent) "changed output"
  let storage ← checked (row.getObjValAs? (Array Json) "committedStorage")
  rejects (validateManifest (withRow (row.setObjVal! "committedStorage"
    (.arr (storage.set! 8 (storage[8]!.setObjVal! "value" (toJson "7")))))) parent) "changed slot"
  rejects (validateManifest (replace first (first.setObjVal! "expectedHistory" (.arr history.pop))) parent) "popped history"
  let plan ← checked (first.getObjVal? "storageLoopPlan")
  rejects (validateManifest (replace first (first.setObjVal! "storageLoopPlan" (plan.setObjVal! "form" (toJson "pipelined"))))
    parent) "changed form"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr entries.pop)) parent) "dropped entry"
  rejects (validateManifest (manifest.setObjVal! "cases" (.arr (entries.push first))) parent) "duplicated entry"
  for (key, value) in [
      ("profile", toJson "stateful-storage-loops"), ("emitterVersion", toJson "forged"),
      ("requiredMasks", toJson [1, 3, 7]), ("requiredForms", toJson ["split", "carried"]),
      ("requiredFormIterations", toJson ["split:0"]), ("requiredFormCarries", toJson ["split:iteration"])] do
    rejects (validateManifest (manifest.setObjVal! key value) parent) key
  rejects (validateManifest manifest (parent.setObjVal! "cases" (.arr #[]))) "another parent corpus"
  rejects (validateManifest manifest parent 0) "no fuel"
  IO.println summary.compress

end Tests.SourceAssemblyStorageLoopCorpus
