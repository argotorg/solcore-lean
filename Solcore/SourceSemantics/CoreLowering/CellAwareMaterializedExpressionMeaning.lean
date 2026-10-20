import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics

/-! The actual compiler certificate supplies meaning and positive output
provenance for generalized reads, groups and products. The body consumer
receives no expression execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include sourceEq runtime selectedBodies covers in
/-- Every accepted expression in the bounded compiler profile preserves its
original Source execution, including reached mixed cells and public failures. -/
theorem preserves_selected (size : Nat) :
    CellAwareMaterializedScopeBounds.PreservesAt bridge context model named stages invocation
      (CellAwareMaterializedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ selectedBodies.signatures
  exact CellAwareMaterializedExpressionTreeBounds.preserves_tree (bodyRegistry := bodyRegistry)
    (semanticFaults := semanticFaults) generation bridge profile runtime.graph.nodeOccurrencesUnique
    (CellAwareNamedGeneralizedReadBounds.preserves bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog) tree size ⟨rfl, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include sourceEq runtime wellFormed covers in
theorem preserves (size : Nat) :
    CellAwareMaterializedScopeBounds.PreservesAt bridge context model named stages invocation
      (CellAwareMaterializedBodyProducer.Certificate generation context) callFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (sourceEq := sourceEq) (runtime := runtime) (covers := covers) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionMeaning
