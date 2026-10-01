import Solcore.Frontend.SourceCoreCallableAncestryPrograms
import Solcore.Frontend.SourceCoreCallableAncestryLedger
import Solcore.Frontend.SourceCoreCallableAncestryPreparation
import Solcore.Frontend.ProgramChecking

set_option autoImplicit false
namespace Tests.SourceCoreCallableSharedHistory
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) { let shared = lam(item) { let probe: Word = 0; return item; }; let outer = lam(value) { keep(value); return shared(value); }; return outer(seed); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"shared ancestry fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let owner ← key program "sharedHistory"
  let plan ← match SourceSpecializationWorklist.run program [⟨owner.declaration, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"shared ancestry worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"shared ancestry base failed: {reprStr error}")
private def initial : SourceCoreAllocationLedger.SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

/-- Ground instances discovered under a read-parent are compiled at the
original lexical bundle-creation scope. This is a positive compiler regression;
it does not claim the scoped single-parent ancestry table covers this case. -/
def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"shared source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"shared compiler failed: {reprStr error}")
  for fuel in [0, 31, 100000] do
    let completion ← match prepared.runSource (← key program "sharedHistory") [.word (w 3)] fuel 500 with
      | .ok completion => pure (completion.resume 100000)
      | .error error => throw (IO.userError s!"shared native run failed: {reprStr error}")
    match completion.result.native.observation with
    | .succeeded (.word result) _ => assertTrue (result == w 3) "shared bundle candidate changed execution"
    | other => throw (IO.userError s!"shared bundle did not complete: {reprStr other}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"shared ledger failed: {reprStr error}")
    for name in ["shared", "item", "probe"] do
      assertTrue (ledger.ledger.rows.any (·.entry.key.binder.name == name)) s!"shared source allocation {name} disappeared"
    let shared ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some shared => pure shared | none => throw (IO.userError "shared bundle marker missing")
    assertTrue (shared.environment.map Prod.fst == shared.entry.key.scope.map Prod.fst)
      "read-parent preparation changed source lexical capture order"
    assertTrue (shared.environment.length == 1) "shared bundle captured a read-parent parameter"
    let capturedSeed ← match shared.environment.head? with
      | some binding => pure binding | none => throw (IO.userError "shared bundle dropped lexical seed capture")
    let seed ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "seed") with
      | some seed => pure seed | none => throw (IO.userError "shared seed allocation missing")
    assertTrue (capturedSeed.1 == seed.entry.key.binder.id && capturedSeed.2 == seed.sourceLocation)
      "shared bundle selected the read parent's environment instead of its creation environment"
    assertTrue (SourceCoreCallableAncestryLedger.frame? completion == some .empty)
      "shared bundle left an active callable frame"
  IO.println "root-created generic bundle: authenticated read-parent recipe, lexical captures and typed Core resume GREEN"

/-- Read-only regression audit for a root-created generalized lambda invoked
inside another generalized lambda. An unavailable transition is reported as
false; this audit is separate from the read-wrapper authentication contract. -/
def auditShared : IO Bool := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"shared ancestry source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"shared ancestry compiler failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPreparation.prepare automatic.prepared with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"shared ancestry graph failed: {reprStr error}")
  let completion ← match prepared.runSource (← key program "sharedHistory") [.word (w 3)] 100000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"shared ancestry native run failed: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word result) _ => assertTrue (result == w 3) "shared ancestry changed execution"
  | other => throw (IO.userError s!"shared ancestry did not complete: {reprStr other}")
  let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"shared ancestry ledger failed: {reprStr error}")
  let mut available := true
  for row in ledger.ledger.rows do
    let snapshot ← match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot | .error error => throw (IO.userError s!"shared allocation snapshot failed: {reprStr error}")
    let state := (graph.table.lookup? snapshot.frame).map (·.map fun state => (state.owner, state.active))
    IO.println s!"shared ancestry allocation {row.entry.key.binder.name}: frame={reprStr snapshot.frame}, state={reprStr state}"
    if row.entry.key.binder.name == "probe" then available := state.isSome
  let current ← match SourceCoreCallableAncestryLedger.frame? completion with
    | some current => pure current | none => throw (IO.userError "shared ancestry final frame missing")
  assertTrue (graph.table.lookup? current == some none) "shared ancestry failed to restore empty current frame"
  IO.println s!"root-created shared lambda's nested read transition available: {available}"
  pure available

end Tests.SourceCoreCallableSharedHistory
