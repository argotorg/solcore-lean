import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer

/-! Projected assignment children consume admission at the real key and getter
states. The independent original Source key row supplies actual child typing;
its types are not equated with the layout's representation vector. Successful
writes retain admission at the exact reached prefix, while faults retain stable
histories and the original independently measured continuation receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedProjectedAssignmentHeads
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

section Rhs
variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {codes : List SourceCoreBasic.LoweredExpr}
  {sourceTypes : List TypeSystem.Ty} {leaf type : TypeSystem.Ty}
  {environment : Dynamic.Environment} {actual canonical : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrative actualContext : Core.Context} {certificate : Certificate}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (targetTyped : SourcePlaceHasType source context place type)
  (sourceTyped : ExpressionHasType source context id node.type)
  (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
    mapping world administrative scope environment canonical)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include admitted wellFormed runtime covers targetTyped sourceTyped generated found environments locals agrees actualTyped in
/-- A genuine resolution establishes Source heap admission at its same actual
getter post before the strict RHS child executes under the three saved slots. -/
theorem rhs_preserves_after (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel checked registry functions)
        context evidence source certificate faults size)) :
    ProtectedPlaceRhs.PreservesAfter (checked := checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := actual) (ξ := ξ) callerProtocol initial budget := by
  intro target targetHeap resolved resolution reached _related size outcome after smaller trace
  have getterAdmission := CallableIndexedOwnedPlaceAdmission.after_resolution bridge context initial reached admitted
    wellFormed runtime covers locals targetTyped resolved resolution.frame
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      finalState, related, _post⟩ :=
    meaning size smaller generated found sourceTyped (environments.extend resolution.maps resolution.worlds)
      resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values,
          .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (ProtectedPlaceRhs.snapshot_runtimeTyped resolution actualTyped) reached getterAdmission trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ProtectedPlaceRhs.rhs_of_expression resolution callerProtocol reached trace.sound ?_ represented
      finalHeaps maps worlds frame metadata ⟨finalState, related⟩⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

include admitted wellFormed runtime covers targetTyped sourceTyped generated found environments locals agrees actualTyped in
/-- Native RHS reflection consumes that same genuine getter post and retains
its independently measured Source child and actual result state. -/
theorem rhs_reflects_after (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel checked registry functions)
        context evidence source certificate faults size)) :
    ProtectedPlaceRhs.ReflectsAfter (checked := checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := actual) (ξ := ξ) callerProtocol initial budget := by
  intro target targetHeap resolved resolution reached _related size value finalStore smaller evaluated
  have getterAdmission := CallableIndexedOwnedPlaceAdmission.after_resolution bridge context initial reached admitted
    wellFormed runtime covers locals targetTyped resolved resolution.frame
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      finalState, related, _post⟩ :=
    meaning size smaller generated found sourceTyped (environments.extend resolution.maps resolution.worlds)
      resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values,
          .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (ProtectedPlaceRhs.snapshot_runtimeTyped resolution actualTyped) reached getterAdmission
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    ProtectedPlaceRhs.rhs_of_expression resolution callerProtocol reached trace.sound evaluated.sound represented
      finalHeaps maps worlds frame metadata ⟨finalState, related⟩⟩
end Rhs

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
/-- The completed projected write exposes its actual seven-slot prefix and
success admission separately from the continuation. -/
theorem preserves_prefix_bounded (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) {updated : Dynamic.Value} {after : Dynamic.Heap}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty _layout => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨_, finalStore, finalMap, finalWorld, _, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation, reached, related⟩ :=
      ProtectedPlaceAssignmentSuccess.Stateful.preserves_prefix_bounded_with_producers budget layout ordinary extension callerProtocol transport faithful observations right found rightView rightType profile
        environments heaps locals agrees actualTyped initial
        (fun target _ hiddenTyped => CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted
          layout.children unique keyTyped environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          hiddenTyped budget boundedMeaning)
        (rhs_preserves_after bridge initial admitted wellFormed runtime covers targetTyped sourceTyped right found
          environments locals agrees actualTyped budget boundedMeaning)
        slot writable trace bounded invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, typed,
      ⟨reached, related, CallableIndexedOwnedAssignmentAdmission.after_assignment_sized bridge context
        initial reached admitted wellFormed runtime covers locals assignmentTyped trace frame⟩, continuation⟩

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected in
/-- A fault retains the actual latest key, getter or RHS state and every row's
stable history without claiming deep typing of a fault heap. -/
theorem preserves_fault_reachable_bounded (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (errors : head.ReachableErrors registry faults)
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
  cases shape with
  | bare empty _layout => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      ProtectedPlaceAssignmentFaults.Stateful.preserves_bounded_with_producers budget layout ordinary extension callerProtocol transport faithful observations
        errors.missing errors.uninitialized right found rightView rightType profile environments heaps locals agrees actualTyped initial
        (fun target _ hiddenTyped => CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted
          layout.children unique keyTyped environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          hiddenTyped budget boundedMeaning)
        (rhs_preserves_after bridge initial admitted wellFormed runtime covers targetTyped sourceTyped right found
          environments locals agrees actualTyped budget boundedMeaning)
        slot writable trace bounded next output invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers projected in
/-- Native success restores admission at the actual written prefix and keeps
its strict remaining continuation, distinct from the eventual final store. -/
theorem reflects_reachable_bounded (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (functionTypes : FunctionRuntimeViews functions)
    (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size values.checked registry functions context evidence source faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | bare empty _layout => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have result := ProtectedPlaceAssignmentReflection.Stateful.reflects_bounded_with_producers budget layout ordinary extension callerProtocol transport functionTypes faithful observations
      errors.missing errors.uninitialized right found rightView rightType profile environments heaps agrees actualTyped initial
      (fun target _ hiddenTyped => CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted
        layout.children unique keyTyped environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
        hiddenTyped budget boundedReflection)
      (rhs_reflects_after bridge initial admitted wellFormed runtime covers targetTyped sourceTyped right found
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
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedProjectedAssignmentHeads
