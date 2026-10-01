import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewCalls
import Solcore.Test.SourceCoreCallableIndexedLambdaCalls

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation.Body.source
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaViewCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaViewInvocation CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
section Proof
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : SourceSemantics.Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem completed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Core.Value} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaViewCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inRight .word result) finalStore) :
    ∃ sourceResult after finalMap finalWorld,
      Dynamic.CallableApplies program callerContext callerEvidence function.evidence before (.closure function) arguments sourceResult after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile)).Represents
        finalMap finalWorld function.resultType sourceResult result code.receipt.resultCore ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaViewCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | value payload =>
    cases execution with
    | value called => exact ⟨_, after, finalMap, finalWorld, called, payload, finalHeap, caller.read⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem failed_call {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {token : Word} {finalStore : Store} {fuel : Nat}
    (completed : runStateful fuel (.initial CallableIndexedLambdaViewCalls.applyPayload
      [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments] store)
      = .done (.inLeft code.receipt.resultCore (.word token)) finalStore) :
    ∃ reason after finalMap finalWorld,
      Dynamic.CallableFaults program callerContext callerEvidence function.evidence before (.closure function) arguments reason after ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      finalStore.read? location = some (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨outcome, after, finalMap, finalWorld, execution, related, finalHeap, _, _, _, _, caller⟩ :=
    CallableIndexedLambdaViewCalls.reflects captured code history body profile extension represented heaps locals reference read
      currentCarried unmapped allowed uninitialized missing (runStateful_evaluation_sound completed)
  cases related with
  | fault represented =>
    cases execution with
    | fault failed => exact ⟨_, after, finalMap, finalWorld, failed, represented, finalHeap, caller.read⟩
end Proof

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }" }] }

/-- The view changes the enclosing expression header, while the actual
parameter site and allocator still use the same complete binder metadata.
This checks allocation authentication only; it does not assert that arbitrary
header replacement preserves the source body semantics. -/
private def allocationView : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "lambda view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "lambda view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"lambda view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "lambda view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "lambda view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let lambda ← match prepared.ancestry.templates.lambdas with
    | lambda :: _ => pure lambda
    | [] => throw (IO.userError "lambda view template missing")
  let parameter ← match lambda.node.form with
    | .lambda (parameter :: _) _ _ => pure parameter
    | _ => throw (IO.userError "lambda view parameter missing")
  let site ← match prepared.layouts.entries.find? (fun site => decide
      (site.key.owner = lambda.owner ∧ site.key.active = lambda.active ∧ site.key.binder = parameter ∧ site.key.initialized = true)) with
    | some site => pure site
    | none => throw (IO.userError "lambda view actual parameter site missing")
  let source := lambda.context.inventory.source
  let view := SourceCoreEvidence.withNode source { lambda.node with type := .bool }
  SourceCompilerFeatureSupport.require (decide (source ≠ view)) "view fixture failed to change its full source"
  SourceCompilerFeatureSupport.require
    (decide (SourceCoreAllocationCodebook.sourceView source = SourceCoreAllocationCodebook.sourceView view))
    "lambda metadata view changed authenticated source shape"
  let request : SourceCoreSourceCells.Request :=
    ⟨source, site.key.scope, Renaming.id, parameter, site.key.payloadType, some (.var 0)⟩
  let original ← SourceCompilerFeatureSupport.get "lambda original allocation"
    (SourceCoreAllocationLayouts.allocateWithReceipt prepared.layouts lambda.owner lambda.active request)
  let viewed ← SourceCompilerFeatureSupport.get "lambda metadata-view allocation"
    (SourceCoreAllocationLayouts.allocateWithReceipt prepared.layouts lambda.owner lambda.active {request with source := view})
  SourceCompilerFeatureSupport.require (original.expression == viewed.expression)
    "metadata view changed actual parameter captures or payload allocation"
  SourceCompilerFeatureSupport.require (decide (original.entry.key = viewed.entry.key))
    "metadata view selected a different allocation layout"

def run : IO Unit := do
  allocationView
  Tests.SourceCoreCallableIndexedLambdaCalls.run
  IO.println "indexed lambda metadata views: unequal source tables preserve actual parameter allocation and canonical-source call receipts GREEN"
end Tests.SourceCoreCallableIndexedLambdaViewCalls
