import Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
import Solcore.Frontend.SourceCoreCallableAncestryPreparation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Header.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Restored.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.AllocationRestored.mk

/-! Actual finite graph preparation happens before native execution. Unused
generalized principals retain open lambda headers, occurrence-specific source
metadata and ordered source captures despite having a Unit native payload.
This test does not assert that every accepted artifact's preparation completes.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPrincipalHeaders
open Solcore Solcore.Frontend SourceInference
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value
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
    | .ok program => pure program | .error error => throw (IO.userError s!"principal header source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.find? (·.name == "unusedViews") with
    | some signature => pure signature | none => throw (IO.userError "principal header root missing")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"principal header plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"principal header base failed: {reprStr error}")
  let native ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"principal header compiler failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPreparation.prepare automatic.prepared with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"principal header graph preparation failed: {reprStr error}")
  let headers ← match SourceCoreCallableAncestryPrincipalHeaders.prepare native graph.table with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"principal header preparation failed: {reprStr error}")
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer 12)⟩, ⟨.bool, some (.bool true)⟩]
  for budget in [0, 31, 211, 100000] do
    let completion ← match native.runSource key [.word (w 4)] budget with
      | .ok completion => pure (completion.resume 100000)
      | .error error => throw (IO.userError s!"principal header native call failed: {reprStr error}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"principal header ledger failed: {reprStr error}")
    let rows := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (rows.length == 2) "unused principal allocation count changed"
    let sources ← rows.mapM fun row => do
      assertTrue (row.payload == some Core.Value.unit) "unused principal acquired native executable code"
      let allocation ← match SourceCoreCallableAncestryPrincipalHeaders.restoreAllocation headers row with
        | .ok restored => pure restored | .error error => throw (IO.userError s!"principal restoration failed: {reprStr error}")
      let restored := allocation.restored
      match restored.value with
      | .closure parameters result body source owner captured evidence =>
        assertTrue (!result.freeVariables.isEmpty && parameters.length == 1 && !body.isEmpty)
          "unused generic principal lost its open source header"
        assertTrue (owner == key && reprStr captured == reprStr row.environment)
          "principal owner or ordered capture locations changed"
        assertTrue (captured.all fun entry => initial.length ≤ entry.2.index)
          "principal captures included the opaque initial prefix"
        assertTrue (reprStr evidence == reprStr restored.header.principal.context.evidence)
          "principal cached evidence changed"
        pure (reprStr source)
      | _ => throw (IO.userError "principal restoration erased the source closure constructor")
    assertTrue (sources.eraseDups.length == 2) "same-type reads lost distinct principal requirement metadata"
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == w 8) "principal preparation changed native execution"
    | _ => throw (IO.userError "principal header source did not complete")
  IO.println "prepared principal headers: unused generic Unit bundles, raw sources, ordered captures and resume GREEN"

end Tests.SourceCoreCallableAncestryPrincipalHeaders
