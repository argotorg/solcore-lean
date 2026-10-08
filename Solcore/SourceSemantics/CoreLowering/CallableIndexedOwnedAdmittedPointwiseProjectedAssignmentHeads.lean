import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedProjectedAssignmentHeads

/-! Admitted projected heads consume only their real reached diagnostic
phase. Original ordered key/RHS producers, all actual pool records, the written
seven-slot prefix and strict continuation bounds remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique source)
  (assignmentTyped : SourceAssignmentHasType source context assignment operator rhs)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected in
/-- A fault retains the actual latest key, getter or RHS state and every row's
stable history without claiming deep typing of a fault heap. -/
theorem preserves_fault_with_diagnostics (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before assignment.target operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol source context certificate
    scope administrative environment assignment.target prepared operator invalid initial faults shape at errors
  cases errors with
  | @bare empty layout operands => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      ProtectedPlaceAssignmentFaults.Stateful.preserves_bounded_with_producers_with_diagnostics budget layout ordinary extension callerProtocol transport faithful observations
        right found rightView rightType profile environments heaps locals agrees actualTyped initial missing uninitialized
        (fun target _ hiddenTyped => CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted
          layout.children unique keyTyped environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          hiddenTyped budget boundedMeaning)
        (CallableIndexedOwnedAdmittedProjectedAssignmentHeads.rhs_preserves_after bridge initial admitted wellFormed runtime covers targetTyped sourceTyped right found
          environments locals agrees actualTyped budget boundedMeaning)
        slot writable trace bounded next output invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected in
/-- Native success restores admission at the actual written prefix and keeps
its strict remaining continuation, distinct from the eventual final store. -/
theorem reflects_with_diagnostics (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (functionTypes : FunctionRuntimeViews functions)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial faults head.shape)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size values.checked registry functions context evidence source faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol source context certificate
    scope administrative environment assignment.target prepared operator invalid initial faults shape at errors
  cases errors with
  | @bare empty layout operands => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have result := ProtectedPlaceAssignmentReflection.Stateful.reflects_bounded_with_producers_with_diagnostics budget layout ordinary extension callerProtocol transport functionTypes faithful observations
      right found rightView rightType profile environments heaps agrees actualTyped initial missing uninitialized
      (fun target _ hiddenTyped => CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted
        layout.children unique keyTyped environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
        hiddenTyped budget boundedReflection)
      (CallableIndexedOwnedAdmittedProjectedAssignmentHeads.rhs_reflects_after bridge initial admitted wellFormed runtime covers targetTyped sourceTyped right found
        environments locals agrees actualTyped budget boundedReflection)
      locals slot writable completed bounded
    cases result with
    | fault trace same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .fault trace same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | committed trace finalHeaps maps worlds frame metadata count typed post strict remaining =>
      obtain ⟨reached, related⟩ := post
      exact .success trace finalHeaps maps worlds frame metadata count typed reached related
        (CallableIndexedOwnedAssignmentAdmission.after_assignment_sized bridge context
          initial reached admitted wellFormed runtime covers locals assignmentTyped trace frame) strict remaining
end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads
