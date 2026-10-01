import Solcore.Frontend.SourceCoreCallablePairedHeaders
import Solcore.Frontend.SourceCoreCallablePairedPrincipalAllocations
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.PrincipalHeader.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.LambdaHeader.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.Prepared.mk

/-! The cache stores raw principal headers from actual paired source states.
Open unused principals survive even when the native context also contains an
unrelated caller substitution. Capture provenance is tested by runtime joins. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedHeaders
open Solcore Solcore.Frontend SourceInference
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let unused = lam(value) { return value; }; let local = lam(value: Word) -> Word { return value; }; local(0); return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }"
  ]}] }

def run : IO Unit := do
  let program ← get "paired header checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "sharedHistory") with
    | some signature => pure signature | none => throw (IO.userError "missing paired header root")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"paired header plan failed: {reprStr other}")
  let automatic ← get "paired header compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let graph ← get "paired header graph" (SourceCoreCallableAncestryPairedPreparation.prepare automatic.prepared)
  let headers ← get "paired raw headers" (SourceCoreCallablePairedHeaders.prepare graph)
  let mut different := 0
  for header in headers.principalHeaders do
    if header.principal.principal.binder.name == "unused" && header.state.metadata.active != header.state.nativeActive then
      assertTrue (!header.resultType.freeVariables.isEmpty) "unused principal lost its open source result"
      assertTrue (header.parameters.length == 1 && !header.body.isEmpty) "raw lambda header was discarded"
      let cell := header.cell []
      assertTrue (cell.type == header.declaration.binder.scheme.body) "source cell type came from the native binder"
      match cell.value with
      | some (.closure parameters result body source owner captured evidence) =>
        assertTrue (parameters == header.parameters && result == header.resultType && body == header.body &&
          source == header.state.metadata.source && owner == header.state.metadata.owner &&
          captured.isEmpty && reprStr evidence == reprStr header.principal.context.evidence)
          "principal restoration changed raw metadata, captures or evidence"
      | _ => throw (IO.userError "unused principal native bundle replaced its source closure")
      if header.state.metadata.source != header.principal.context.source then different := different + 1
  assertTrue (different > 0) "missing distinct source/native principal context"
  assertTrue (!headers.lambdaHeaders.isEmpty) "ordinary lambda header cache was empty"
  assertTrue ((headers.lambdaAt? 999999 (Core.Word.ofNatModulo 999999)).isNone) "foreign lambda header accepted"
  let native ← get "paired header native program" (SourceCoreCallablePairedPrograms.prepare automatic.prepared 500)
  let nativeGraph ← get "owned native header graph" (SourceCoreCallableAncestryPairedPreparation.prepare native.base)
  let nativeHeaders ← get "owned native headers" (SourceCoreCallablePairedHeaders.prepare nativeGraph)
  let owner : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer 17)⟩, ⟨.bool, none⟩]
  for budget in [0, 31, 211, 100000] do
    let completion ← get "paired header execution" (native.runSource owner [.word (Core.Word.ofNatModulo 3)] budget)
    let completion := completion.resume 100000
    let ledger ← get "paired header observed ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let rows := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (rows.length == 2) "unused principal allocation count changed"
    for row in rows do
      assertTrue (row.payload == some Core.Value.unit) "unused source principal acquired executable native instances"
      let restored ← get "actual paired principal restoration" (SourceCoreCallablePairedPrincipalAllocations.restore (program := native) nativeHeaders row)
      assertTrue (!restored.header.resultType.freeVariables.isEmpty &&
        restored.header.state.metadata.active != restored.header.state.nativeActive)
        "allocation restoration replaced open raw source metadata with native cumulative context"
      assertTrue (restored.header.state.metadata.source != restored.header.principal.context.source)
        "actual shared allocation lost its lexical source"
      match restored.cell.value with
      | some (.closure _ _ _ source key captured _) =>
        assertTrue (source == restored.header.state.metadata.source && key == owner && captured.length == 2 &&
          captured.all (fun entry => initial.length ≤ entry.2.index)) "actual principal captures lost source prefix or lexical scope"
      | _ => throw (IO.userError "actual Unit principal was not restored to a source closure")
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == Core.Word.ofNatModulo 6) "paired principal restoration changed computation"
    | _ => throw (IO.userError "paired principal execution did not finish")
  IO.println "paired cached raw headers: unused open principals, ordinary lambdas, separate source/native contexts GREEN"

end Tests.SourceCoreCallablePairedHeaders
