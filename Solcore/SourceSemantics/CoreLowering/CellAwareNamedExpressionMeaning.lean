import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueOrigins
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedReadDiagnostics

/-! The actual finite named compiler certificate supplies complete expression
meaning. Ordinary reads, generalized instantiation and real application are
all discharged here; the body consumer receives no expression or call law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
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
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := compiled) named invocation)
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
  (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (covers : invocation.evidence.Covers context)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
/-- Every accepted expression in the bounded compiler profile preserves its
original Source execution, including reached mixed cells and public failures. -/
theorem preserves (size : Nat) :
    CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ wellFormed.signatures
  exact CellAwareNamedExpressionTreeBounds.preserves_tree (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) generation bridge profile receiver
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) authority wellFormed runtime covers
    runtime.graph.nodeOccurrencesUnique extension sameLedger runtime.requirements
    (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
    (CellAwarePhysicalFunctionOrigins.observations profile) (CellAwarePhysicalFunctionOrigins.runtime_views profile)
    (CellAwareNamedIndexDiagnostics.ready issuer record sourceEq runtime.graph.nodeOccurrencesUnique)
    (fun _ _ _ read location => CellAwareNamedReadDiagnostics.uninitialized issuer record receiver sourceEq
      runtime.graph.nodeOccurrencesUnique read location)
    (fun _ _ proof => proof)
    (CellAwareBuiltinValueOrigins.included profile)
    (CellAwareNamedGeneralizedReadBounds.preserves bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog)
    (CellAwareNamedGeneralizedApplicationBounds.preserves bridge functions receiver extension runtime wellFormed)
    tree size ⟨rfl, rfl, rfl⟩

include receiver extension authority sourceEq issuer record sameLedger runtime wellFormed covers in
/-- Finite Core completion reconstructs the independent Source grade and the
same returned state through the actual accepted compiler tree. -/
theorem reflects (size : Nat) :
    CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation
      (CellAwareNamedBodyProducer.Certificate generation context) callFaults size := by
  intro scope id lowered certificate node
  obtain ⟨rootFuel, tree⟩ := certificate
  rw [← sourceEq] at tree
  have catalog : SignatureCatalogWellFormed context.signatures := runtime.signatures.symm ▸ wellFormed.signatures
  exact CellAwareNamedExpressionTreeBounds.reflects_tree (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) generation bridge profile receiver
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) authority wellFormed runtime covers
    runtime.graph.nodeOccurrencesUnique extension sameLedger runtime.requirements
    (CallableIndexedLambdaValues.identity_faithful compiled.indexed)
    (CellAwarePhysicalFunctionOrigins.observations profile) (CellAwarePhysicalFunctionOrigins.runtime_views profile)
    (CellAwareNamedIndexDiagnostics.ready issuer record sourceEq runtime.graph.nodeOccurrencesUnique)
    (fun _ _ _ read location => CellAwareNamedReadDiagnostics.uninitialized issuer record receiver sourceEq
      runtime.graph.nodeOccurrencesUnique read location)
    (fun _ _ proof => proof)
    (CellAwareBuiltinValueOrigins.included profile)
    (CellAwareNamedGeneralizedReadBounds.reflects bridge profile runtime.graph.nodeOccurrencesUnique
      runtime.requirements.idsUnique covers catalog)
    (CellAwareNamedGeneralizedApplicationBounds.reflects bridge functions receiver extension runtime wellFormed)
    tree size ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionMeaning
