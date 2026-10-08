import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedShapeDiagnostics

/-! Public projected endpoints derive reached diagnostics from the same
retained Source occurrence and accepted preparation. Existing admitted head
cores keep the actual ordered producers, pool and strict continuation bounds. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
variable (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (header.function.source) context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique (header.function.source))
  (assignmentTyped : SourceAssignmentHasType (header.function.source) context assignment operator rhs)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context (header.function.source))
  (covers : evidence.Covers context)

variable (receipt : CallableIndexedOwnedPublicPreparedTokenReadyNamedExpressionBounds.PublicReceipt header)
  {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
  (diagnosticsFound : compiled.indexed.base.diagnostics = some diagnostics)
  {site : SourceCoreElaboration.ErrorSite}
  (origin : AssignmentDiagnosticOrigins.Occurs (header.function.source) site assignment operator rhs)
  {fuel : Nat}
  (retained : head.PreparedAt site fuel
    (receipt.original.prepared.diagnostics.placeReason header.named.signature.key site assignment.target.root none)
    (fun rawValue => receipt.original.prepared.diagnostics.placeReason header.named.signature.key
      site assignment.target.root (some rawValue)))
  (signatures : context.signatures = compiled.compatible.checked.signatures)
  {table : SourceCoreFaultSites.Table}
  (rebuilt : diagnostics.tableForRegistry registry extension = .ok table)
  (interprets : CallableIndexedOwnedPublicPreparedShapeDiagnostics.ReachedTableInterpretation
    compiled.compatible.checked registry functions callerProtocol environment assignment.target head.prepared initial table faults)

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected receipt diagnosticsFound origin retained signatures rebuilt interprets in
/-- A fault retains the actual latest key, getter or RHS state and every row's
stable history without claiming deep typing of a fault heap. -/
theorem preserves_fault (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel compiled.compatible.checked registry functions)
        context evidence (header.function.source) certificate faults size))
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults (Program.ofChecked compiled.sourceProgram) size context evidence (header.function.source) environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  have errors := CallableIndexedOwnedPublicPreparedShapeDiagnostics.shape_errors_at_header
    header head initial receipt diagnosticsFound projected origin retained assignmentTyped signatures rebuilt interprets
  exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.preserves_fault_with_diagnostics
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    bridge functions extension evidence transport faithful observations head projected environments heaps locals agrees
    actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedMeaning errors trace bounded next output

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected receipt diagnosticsFound origin retained signatures rebuilt interprets in
/-- Native success restores admission at the actual written prefix and keeps
its strict remaining continuation, distinct from the eventual final store. -/
theorem reflects (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel compiled.compatible.checked registry functions)
        context evidence (header.function.source) certificate faults size)) (functionTypes : FunctionRuntimeViews functions)

    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size compiled.compatible.checked registry functions context evidence (header.function.source) faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  have errors := CallableIndexedOwnedPublicPreparedShapeDiagnostics.shape_errors_at_header
    header head initial receipt diagnosticsFound projected origin retained assignmentTyped signatures rebuilt interprets
  exact CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads.reflects_with_diagnostics
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    bridge functions extension evidence transport faithful observations head projected environments heaps locals agrees
    actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedReflection functionTypes errors completed bounded

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPreparedProjectedAssignmentHeads
