import Solcore.Frontend.SourceCorePlanCatalog
import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.SourceSemantics.CoreLowering.CallEntryCertificates
import Solcore.SourceSemantics.CoreLowering.CallCodebookCertificates

/-! Checked local instances retain their source inventory while projecting
their mapping parameter and result through the selected representation.
Callable origins, IDs and decisions still come from original source metadata. -/
set_option autoImplicit false
namespace Tests.SourceCoreRepresentationProjection
open Solcore Solcore.Frontend SourceInference

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return item; }; return f(table); }"}]
}

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    (accepted : SourceCoreStageCodebook.prepareWithProjection program plan projectType limits firstId = .ok table) :
    SourceSemantics.CoreLowering.CallEntryCertificates.AllAuthenticated plan table.entries :=
  SourceSemantics.CoreLowering.CallEntryCertificates.prepareWithProjection_authenticates accepted

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"projection fixture rejected: {reprStr error}")
  let signature ← match program.signatures.functions.filter (·.name == "local") with
    | [signature] => pure signature
    | _ => throw (IO.userError "projection root missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 64 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"projection discovery failed: {reprStr result}")
  let plan ← match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
    | .ok plan => pure plan
    | .error error => throw (IO.userError s!"projection plan failed: {reprStr error}")
  let discovered ← match SourceCompilationPlan.localLambdaCatalog plan with
    | .ok discovered => pure discovered
    | .error error => throw (IO.userError s!"projection local discovery failed: {reprStr error}")
  let types := (SourceCorePlanCatalog.planTypes plan ++ discovered.flatMap (fun entry =>
    SourceCorePlanCatalog.sourceTypes (entry.source.applySubstitution entry.substitution))).filter
      SourceCoreDataCatalog.closed |>.eraseDups
  let strict ← match SourceCoreDataCatalog.prepare program.signatures 256 types true with
    | .ok strict => pure strict
    | .error error => throw (IO.userError s!"strict projection failed: {reprStr error}")
  let compatible ← match SourceCoreCompatibleCatalog.prepare program.signatures 256 types with
    | .ok compatible => pure compatible
    | .error error => throw (IO.userError s!"compatible projection failed: {reprStr error}")
  let project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty := fun type =>
    (compatible.project type).map (·.type) |>.mapError fun _ => .initializerMetadataMismatch ⟨⟨signature.id, 0⟩⟩
  let locals ← match SourceCoreLocalPolymorphism.prepareWithProjection project plan with
    | .ok locals => pure locals
    | .error error => throw (IO.userError s!"compatible local projection failed: {reprStr error}")
  let candidate ← match locals.bindings.flatMap (·.instances) with
    | [candidate] => pure candidate
    | _ => throw (IO.userError "projection local instance missing")
  let native ← match compatible.catalog.project (.mapping .word .word) with
    | .ok type => pure type
    | .error error => throw (IO.userError s!"compatible mapping projection failed: {reprStr error}")
  unless candidate.parameterType == native && candidate.resultType == native do
    throw (IO.userError "local mapping instance used another representation")
  let old ← match strict.catalog.project (.mapping .word .word) with
    | .ok type => pure type
    | .error error => throw (IO.userError s!"strict mapping projection failed: {reprStr error}")
  unless old != native do throw (IO.userError "fixture did not distinguish mapping representations")
  let strictTable ← match SourceCoreStageCodebook.prepare program plan strict with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"strict codebook failed: {reprStr error}")
  let compatibleTable ← match SourceCoreStageCodebook.prepareWithProjection program plan project with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"compatible codebook failed: {reprStr error}")
  unless (strictTable.entries.map (fun entry => (entry.id, entry.origin, entry.parameterCount))) ==
      (compatibleTable.entries.map (fun entry => (entry.id, entry.origin, entry.parameterCount))) do
    throw (IO.userError "representation changed callable origins or IDs")
  unless (strictTable.decisions.map (fun row => (row.caller, row.call, row.entry.id, row.argumentCount, reprStr row.answer))) ==
      (compatibleTable.decisions.map (fun row => (row.caller, row.call, row.entry.id, row.argumentCount, reprStr row.answer))) do
    throw (IO.userError "representation changed original stage decisions")
  IO.println "shared representation projection preserves local discovery and callable metadata GREEN"

end Tests.SourceCoreRepresentationProjection
