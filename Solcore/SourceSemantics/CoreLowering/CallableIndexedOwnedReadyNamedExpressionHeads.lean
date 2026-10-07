import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedReadyContinuations

/-! Genuine ordinary and direct named heads consume the shared family's strict
callee meanings at the actual parameter receipt. The original head and caller
protocol are retained, with independent Source and native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission ProtectedStateTransition
open CallableIndexedOwnedAdmittedNamedExpressionHeads
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (runtime : Bool)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {ι : Type}
  (origins : ι → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
  (wellFormed : ProgramWellFormed program)

/-- Static associations cover each genuine parameter receipt. They retain its
whole compiler origin and independent body Syntax, with no execution premise. -/
def AssociationsFor (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Type :=
  ∀ {initial : Index} {argumentsPool : State headers keys initial} {arguments : List Dynamic.Value},
    ∀ receipt : ParameterReceipt (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
      (runtime := runtime) argumentsPool header arguments,
    CallableIndexedOwnedNamedReadyContinuations.Association functions owner runtime origins receipt wellFormed

private abbrev bodyBridge := CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

variable {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → ProfilesFor (headers := headers) (owner := owner) (functions := functions)
    (registry := registry) (faults := faults) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) (runtime := runtime) header)
  (associations : ∀ header, header ∈ headers → AssociationsFor (headers := headers) (certificates := certificates)
    (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) functions owner runtime origins wellFormed header)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)

include wellFormed sourceRuntime covers unique idsUnique sameLayouts escaped profiles associations owners in
/-- Named Source heads use only their strict child expressions and the same
shared family's strict associated body contracts. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.PreservesAt (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  exact CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
    (functions := functions) (owner := owner) (runtime := runtime) evidence bridge wellFormed sourceRuntime covers unique idsUnique
    sameLayouts escaped profiles owners budget size within children
    (fun header member => CallableIndexedOwnedNamedReadyContinuations.source_bodies
      (functions := functions) (owner := owner) (runtime := runtime) (origins := origins)
      wellFormed (associations header member) bodies)

include wellFormed sourceRuntime covers unique sameLayouts escaped profiles associations in
/-- Native head inversion uses the strict native body bound. Its Source result
has an independent grade and the same actual reached parameter pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (bodies : ∀ i, RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocol headers keys)
        (readiness (bodyBridge (headers := headers) (keys := keys))) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
        (ProtectedStateImperativeTypedSourceSites.Facts (origins i).function.source (origins i).expressionSyntax)
        functions program (origins i))) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  exact CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
    (functions := functions) (owner := owner) (runtime := runtime) evidence bridge wellFormed sourceRuntime covers unique
    sameLayouts escaped profiles budget size within children
    (fun header member => CallableIndexedOwnedNamedReadyContinuations.native_bodies
      (functions := functions) (owner := owner) (runtime := runtime) (origins := origins)
      wellFormed (associations header member) bodies)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReadyNamedExpressionHeads
