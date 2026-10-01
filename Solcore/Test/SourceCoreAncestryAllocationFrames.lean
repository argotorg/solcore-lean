import Solcore.Frontend.SourceCoreCallableAncestryLedger
import Solcore.Frontend.ProgramChecking

/-! Allocation snapshots preserve unused generalized principals' dynamic
ancestry, through the actual two-pass compiler and its typed native runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreAncestryAllocationFrames
open Solcore Solcore.Frontend SourceInference
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function unusedViews(seed: Word) returns (Word) {",
    " let outer = lam(value) { keep(value); let unused = lam(item) { return item; }; return seed; };",
    " return outer(1) + outer(2); }"
  ]}] }

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"allocation frame source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.find? (·.name == "unusedViews") with
    | some signature => pure signature | none => throw (IO.userError "allocation frame root absent")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"allocation frame plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"allocation frame base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"allocation frame compiler failed: {reprStr error}")
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer (-11))⟩]
  let mut pendingSeen := false
  let mut allocationSeen := false
  for budget in List.range 600 do
    let suspended ← match prepared.runSource key [.word (w 4)] budget with
      | .ok suspended => pure suspended
      | .error error => throw (IO.userError s!"allocation frame checkpoint failed: {reprStr error}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan suspended initial with
      | .ok ledger => pure ledger
      | .error error => throw (IO.userError s!"allocation frame checkpoint ledger failed: {reprStr error}")
    pendingSeen := pendingSeen || ledger.ledger.pending.isSome
    allocationSeen := allocationSeen || !ledger.ledger.rows.isEmpty
    for row in ledger.ledger.rows do
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok _ => pure ()
      | .error error => throw (IO.userError s!"checkpoint source allocation lost its preceding frame: {reprStr error}")
      assertTrue (initial.length ≤ row.sourceLocation.index &&
        row.environment.all (fun entry => initial.length ≤ entry.2.index))
        "administrative frame cells entered source locations or captures"
  assertTrue pendingSeen "allocation snapshot test missed a marker-only checkpoint"
  assertTrue allocationSeen "allocation snapshot test missed a completed source cell"
  for budget in [0, 7, 31, 67, 150000] do
    let completion ← match prepared.runSource key [.word (w 4)] budget with
      | .ok completion => pure completion | .error error => throw (IO.userError s!"allocation frame native run failed: {reprStr error}")
    let completion := completion.resume 150000
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"allocation frame ledger failed: {reprStr error}")
    let snapshots ← ledger.ledger.rows.mapM fun row =>
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot.frame | .error error => throw (IO.userError s!"allocation frame snapshot missing: {reprStr error}")
    assertTrue (snapshots.length == ledger.ledger.rows.length) "source rows lost their allocation-time frame"
    let unused := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (unused.length == 2) "unused generalized principal was not allocated on each call"
    assertTrue (unused.all fun row => !row.entry.key.binder.scheme.quantified.isEmpty && row.payload == some .unit)
      "unused generalized principal emitted a native executable closure"
    let histories ← unused.mapM fun row =>
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot.frame | .error error => throw (IO.userError s!"unused principal ancestry absent: {reprStr error}")
    assertTrue (histories.eraseDups.length == 2) "same-type read occurrences lost their distinct principal ancestry"
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == w 8) "allocation frame transport changed source execution"
    | observation => throw (IO.userError s!"allocation frame outcome changed: {reprStr observation}")
  IO.println "allocation-time ancestry for unused generalized source principals GREEN"

end Tests.SourceCoreAncestryAllocationFrames
