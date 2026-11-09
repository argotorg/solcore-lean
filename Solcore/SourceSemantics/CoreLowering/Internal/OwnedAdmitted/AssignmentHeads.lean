import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning

/-!
# Admitted profile: assignments and for headers

Bare and projected assignment heads, pointwise forms, and readiness and bounds of `for` headers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBareAssignmentHeads
/-! Bare assignment Heads use admitted RHS children at their real input and
retain the actual written or fault prefix. Successful Source assignment typing
establishes the next admission; faults retain only actual stable histories. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBareAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
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
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (payloadModel checked registry functions) context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CompatibleBareAssignment.RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ProtectedBareAssignment.rhs_of_expression snapshot callerProtocol initial trace.sound ?_ represented
      finalHeaps maps worlds frame metadata ⟨reached, related⟩⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

private theorem rhs_reflects_at (size : Nat)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (payloadModel checked registry functions) context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      CompatibleBareAssignment.RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    ProtectedBareAssignment.rhs_of_expression snapshot callerProtocol initial trace.sound evaluated.sound represented
      finalHeaps maps worlds frame metadata ⟨reached, related⟩⟩
end Rhs

/-- The native result retains the genuine completed prefix separately from
its still live seven-slot continuation. Only successful writes carry admission. -/
inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FunctionCalls.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before assignment.target operator rhs reason after)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context evidence source faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context evidence source faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

section Heads
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
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

include observations transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers bare in
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
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨_, finalStore, finalMap, finalWorld, slots, _, finalHeaps, maps, worlds, preservation, metadata, count, typed, continuation, reached, related⟩ :=
      ProtectedBareAssignment.Stateful.preserves_prefix_bounded_with_rhs callerProtocol transport budget initial layout empty extension
        (fun snapshot child smaller {_ _} childTrace => rhs_preserves_at bridge snapshot child (boundedMeaning child smaller)
          right found sourceTyped environments heaps locals agrees actualTyped initial admitted childTrace)
        observations right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace bounded invalid
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, preservation, metadata, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      ⟨reached, related, CallableIndexedOwnedAssignmentAdmission.after_assignment_sized bridge context
        initial reached admitted wellFormed runtime covers locals assignmentTyped trace preservation⟩, continuation⟩

include observations extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_fault_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
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
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, reached, related⟩ :=
      ProtectedBareAssignment.Stateful.preserves_fault_reachable_bounded_with_rhs callerProtocol budget initial layout empty extension
        (fun snapshot child smaller {_ _} childTrace => rhs_preserves_at bridge snapshot child (boundedMeaning child smaller)
          right found sourceTyped environments heaps locals agrees actualTyped initial admitted childTrace)
        observations right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace bounded next output invalid errors.operands
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩

include observations transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers bare in
theorem reflects_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context evidence source faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedBareAssignment.Stateful.reflects_reachable_bounded_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted evaluated)
      observations right found rightView rightType profile environments heaps locals agrees actualTyped slot writable errors.operands completed bounded
    cases result with
    | fault trace same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .fault trace same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success trace _ finalHeaps maps worlds preservation metadata count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success trace finalHeaps maps worlds preservation metadata count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related (CallableIndexedOwnedAssignmentAdmission.after_assignment_sized bridge context
          initial reached admitted wellFormed runtime covers locals assignmentTyped trace preservation) strict remaining
end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBareAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedProjectedAssignmentHeads
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
theorem preserves_fault_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
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
        errors.missing (errors.uninitialized layout.nonempty) right found rightView rightType profile environments heaps locals agrees actualTyped initial
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
theorem reflects_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
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
      errors.missing (errors.uninitialized layout.nonempty) right found rightView rightType profile environments heaps agrees actualTyped initial
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedAssignmentHeads
/-! Actual admitted assignment producers select the genuine bare or projected
compiler certificate and retain the same written prefix, fault post and
independent native continuation receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedAssignmentHeads
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

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers in
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
  classical
  by_cases bare : assignment.target.projections = []
  · exact CallableIndexedOwnedAdmittedBareAssignmentHeads.preserves_prefix_bounded bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedMeaning trace bounded
  · exact CallableIndexedOwnedAdmittedProjectedAssignmentHeads.preserves_prefix_bounded bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedMeaning trace bounded

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers in
theorem preserves_fault_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
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
  classical
  by_cases bare : assignment.target.projections = []
  · exact CallableIndexedOwnedAdmittedBareAssignmentHeads.preserves_fault_reachable_bounded bridge functions extension evidence observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped budget boundedMeaning errors trace bounded next output
  · exact CallableIndexedOwnedAdmittedProjectedAssignmentHeads.preserves_fault_reachable_bounded bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedMeaning errors trace bounded next output

include observations faithful transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers in
theorem reflects_reachable_bounded [FunctionCalls.FaultTokens faults] (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (functionTypes : FunctionRuntimeViews functions)
    (errors : head.ReachableErrors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size values.checked registry functions context evidence source faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  classical
  by_cases bare : assignment.target.projections = []
  · exact CallableIndexedOwnedAdmittedBareAssignmentHeads.reflects_reachable_bounded bridge functions extension evidence transport observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedReflection errors completed bounded
  · exact CallableIndexedOwnedAdmittedProjectedAssignmentHeads.reflects_reachable_bounded bridge functions extension evidence transport faithful observations head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers budget boundedReflection functionTypes errors completed bounded

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
/-! Actual Source item facts choose admitted assignment and snapshot producers.
Every returned witness is the original child's reached pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (ValuesContext)
open ProtectedStateTransition ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {values : ValuesContext} {source : TypedSource}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  (transport : AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {faults : FunctionCalls.FaultRep}

include extension transport faithful observations unique wellFormed in
theorem assignment_prefix (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentPrefixPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted updated after size trace bounded
  exact CallableIndexedOwnedAdmittedAssignmentHeads.preserves_prefix_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning trace bounded

include extension transport faithful observations unique wellFormed in
theorem assignment_fault [FunctionCalls.FaultTokens faults] (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentFaultPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted errors reason after size trace bounded next output
  exact CallableIndexedOwnedAdmittedAssignmentHeads.preserves_fault_reachable_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning errors trace bounded next output

include extension transport faithful observations unique wellFormed in
theorem assignment_reflection [FunctionCalls.FaultTokens faults] (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source certificate faults size)) :
    AssignmentReflectsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (SourceAssignmentHasType source) functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head assignmentTyped mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial admitted errors next output value finalStore size evaluated bounded
  have result := CallableIndexedOwnedAdmittedAssignmentHeads.reflects_reachable_bounded bridge functions extension evidence transport
    faithful observations head environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
    wellFormed runtime covers budget meaning functionTypes errors evaluated bounded
  cases result with
  | fault trace same matched heaps maps worlds frame metadata reached related stable =>
    exact .fault trace same matched heaps maps worlds frame metadata ⟨reached, related, stable⟩
  | success trace heaps maps worlds frame metadata count typed reached related admitted smaller remaining =>
    exact .success trace heaps maps worlds frame metadata count typed ⟨reached, related, admitted⟩ smaller remaining

include wellFormed in
theorem snapshot_transfers (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context) :
    SnapshotTransfers callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      validity (SourceBitNotAssignmentValid source) program evidence source where
  ready := by
    intro initial reached first last context assignment environment updated admitted valid typing trace locals frame
    exact (CallableIndexedOwnedSnapshotAdmission.after_snapshot bridge first last admitted wellFormed
      (runtime context valid) (covers context valid) locals typing trace frame).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
/-! Authentic Source item typing and admission feed the existing header and
post producers at their exact reached states. The original Source and native
budgets remain independent; all binder restoration retains the real pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (postValues Progress)
open ProtectedForHeader (Tree)
open ProtectedStateTransition ProtectedForHeader.Stateful ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  {control : ControlContext}

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem preserves_prefix_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor callerProtocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      callerProtocol.Relates state tail.state ∧
      Nonempty (ReadyReturn callerProtocol (readiness bridge) context scope canonical finalContext tail.scope tail.canonical) ∧
      (readiness bridge).Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) ∧
      finalContext = staticFinal ∧ Admission bridge context tail.state ∧
      Admission bridge staticFinal tail.state ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.EnvironmentAgrees after staticFinal.locals finalEnvironment := by
  obtain ⟨tail, maps, worlds, frame, metadata, related, returned, tailReady, continued⟩ := ProtectedForHeader.Stateful.WithReady.Tree.preserves_prefix_bounded_for_with_return
      (functions := functions) (definitions := definitions) (registered := registered)
      (extension := extension) (faithful := faithful) (observations := observations)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      tree valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

  obtain ⟨same, originalReady, finalReady, typedExtension, finalLocals⟩ :=
    CallableIndexedOwnedForItemsAdmission.after_items_sized bridge state tail.state ready
      wellFormed (runtime context valid) (covers context valid) locals itemTyping trace frame
  exact ⟨tail, maps, worlds, frame, metadata, related, returned, tailReady, continued,
    same, originalReady, finalReady, typedExtension, finalLocals⟩

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem preserves_fault_reachable_bounded_for [FunctionCalls.FaultTokens faults]
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition (readiness bridge) state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_fault bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      tree errors valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem reflects_reachable_bounded_for [FunctionCalls.FaultTokens faults]
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor callerProtocol (readiness bridge) condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.reflects_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_reflection bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget functionTypes (boundedReflection context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (boundedReflection context valid child within))
      tree errors valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

variable {context : SourceSemantics.Context} {scope : Scope} {actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem post_preserves_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : condition contextLocation native) (ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).Ready context reached.retained := by
  exact ProtectedForHeader.Stateful.WithReady.post_preserves_bounded_for (solved := [])
    (extension := extension) (faithful := faithful) (observations := observations)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (guard := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      tree valid ⟨staticFinal, itemTyping⟩ agrees reference state read guarded ready continued trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem post_fault_reachable_bounded_for [FunctionCalls.FaultTokens faults]
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : condition contextLocation native) (ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).FaultReady reached.retained := by
  exact ProtectedForHeader.Stateful.WithReady.post_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (guard := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_fault bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      tree errors valid ⟨staticFinal, itemTyping⟩ agrees reference state read guarded ready continued trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem post_reflects_reachable_bounded_for [FunctionCalls.FaultTokens faults]
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (guarded : condition contextLocation native) (ready : (readiness bridge).Ready context state.retained)
    (continued : Bool)
    {size : Nat} (evaluated : EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) (bounded : size ≤ budget) :
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State callerProtocol values registry functions context scope administrative actualContext frame environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ (readiness bridge).FaultReady reached.retained) := by
  exact ProtectedForHeader.Stateful.WithReady.post_reflects_reachable_bounded_for (solved := [])
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (guard := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      validity extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_reflection bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget functionTypes (boundedReflection context valid))
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (boundedReflection context valid child within))
      tree errors valid ⟨staticFinal, itemTyping⟩ agrees reference state read guarded ready continued evaluated bounded


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
/-! Authentic Source item typing and admission feed the existing header and
post producers at their exact reached states. The original Source and native
budgets remain independent; all binder restoration retains the real pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (postValues Progress)
open ProtectedForHeader (Tree)
open ProtectedStateTransition ProtectedForHeader.Stateful ProtectedForHeader.Stateful.WithReady
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  {control : ControlContext}
variable
  (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
  (UP : GenericForHeader.Structural.UnaryPayload)
  (unary : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment),
    UP head → head.Errors faults)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed in
theorem preserves_prefix_from_structural_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor callerProtocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      callerProtocol.Relates state tail.state ∧
      Nonempty (ReadyReturn callerProtocol (readiness bridge) context scope canonical finalContext tail.scope tail.canonical) ∧
      (readiness bridge).Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) ∧
      finalContext = staticFinal ∧ Admission bridge context tail.state ∧
      Admission bridge staticFinal tail.state ∧ Dynamic.HeapTypesExtend before after ∧
      Dynamic.EnvironmentAgrees after staticFinal.locals finalEnvironment := by
  obtain ⟨tree⟩ := GenericForHeader.Structural.tree_of_eliminates receipt
  exact CallableIndexedOwnedAdmittedForHeaderBounds.preserves_prefix_bounded_for
    bridge functions definitions registered extension evidence faithful observations condition producer acquire
    stateTransport stateBindings unique wellFormed validity runtime covers extend budget boundedMeaning
    tree valid itemTyping environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed unary in
theorem preserves_fault_with_payload_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt callerProtocol
      (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget AP)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition (readiness bridge) state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.preserves_fault_reachable_bounded_for_with_eliminator
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      AP UP unary validity
      (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      extend budget
      (fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix bridge functions extension evidence
        stateTransport faithful observations unique wellFormed (runtime context valid) (covers context valid) budget (boundedMeaning context valid))
      assignmentFaults
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (boundedMeaning context valid child within))
      receipt valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered producer acquire stateTransport stateBindings unique wellFormed unary in
theorem reflects_with_payload_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
    (covers : ∀ context, validity context → evidence.Covers context)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) context evidence source (certificates context) faults size))    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (receipt : GenericForHeader.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code)
    (assignments : ∀ context, validity context → AssignmentReflectsWithPayloadAt callerProtocol
      (readiness bridge) (SourceAssignmentHasType source) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget AP)
    (valid : validity context) {staticFinal : SourceSemantics.Context}
    (itemTyping : ForItemsHaveType source control context items staticFinal)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : (readiness bridge).Ready context state)
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor callerProtocol (readiness bridge) condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  exact ProtectedForHeader.Stateful.WithReady.Tree.reflects_reachable_bounded_for_with_eliminator
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := callerProtocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness bridge) (facts := ProtectedStateForHeaderSourceSites.Facts source control)
      (itemFacts := ProtectedStateForHeaderSourceSites.ItemFacts source control)
      (exprFacts := ProtectedStateForHeaderSourceSites.ExpressionFacts source)
      (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
      (sites := ProtectedStateForHeaderSourceSites.sites program evidence source control unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge stateBindings source)
      AP UP unary validity
      (CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed validity runtime covers)
      extend budget
      assignments
      (fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (boundedReflection context valid child within))
      receipt valid ⟨staticFinal, itemTyping⟩ environments heaps locals agrees actualTyped reference read unmapped state gate ready evaluated bounded

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedForHeaderBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
/-! The real native self-cell activation retains the original Source heap.
Its actual administrative effects authenticate every reached row's history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- This producer uses the exact activation endpoint's Source heap index and
real administrative preservation. The reached state and records stay intact. -/
theorem activation : ProtectedFor.Body.Stateful.WithReady.ActivationTransfers callerProtocol
    (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) where
  ready := by
    intro context scope mapping world heap store canonical actual type condition body post reason initial reached
      frame _related _records admitted
    exact ⟨admitted.heap,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
/-! Genuine Source loop facts at the visited initializer context supply the
condition, body, and ordered post sites. The existing measured for endpoint
keeps the actual retained states and independent Source and native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedForContracts (Below)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open TypedLexicalWhile (Scope ValuesContext)

/-- Source control and post-item typing remain attached to the same authentic
body syntax and typing at this exact loop context. -/
def LoopFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (condition : ExpressionId) (post : List ForItemForm)
    (statements : List StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ (control : SourceSemantics.ControlContext) (bodyFinal : SourceSemantics.Context)
    (bodyFacts : SourceSemantics.BodyFacts) (postFinal : SourceSemantics.Context),
    ExpressionHasType source context condition .bool ∧
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements false statements) expected ∧
    StatementsHaveType source control.enterLoop context statements bodyFinal bodyFacts ∧
    ForItemsHaveType source control.enterLoop context post postFinal ∧
    GenericForHeader.Syntax source expressionSyntax context post

namespace LoopFacts

theorem of_done {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    {control : SourceSemantics.ControlContext} {bodyFinal postFinal : SourceSemantics.Context}
    {bodyFacts : SourceSemantics.BodyFacts}
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context
      (.initializers [] condition post statements) expected)
    (bodyTyped : StatementsHaveType source control.enterLoop context statements bodyFinal bodyFacts)
    (postTyped : ForItemsHaveType source control.enterLoop context post postFinal) :
    LoopFacts source expressionSyntax context condition post statements expected := by
  cases syntaxTree with
  | initializersDone _found conditionType typed _conditionSyntax bodySyntax postSyntax =>
    exact ⟨control, bodyFinal, bodyFacts, postFinal,
      by simpa only [conditionType] using typed, bodySyntax, bodyTyped, postTyped, postSyntax⟩

/-- Only this genuine parent Source judgment and actual initializer trace
identify the visited loop context. The normalized syntax is the authentic
remaining initializer site from the same compiler fold. -/
theorem after_initializer {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context loopContext : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (parent : ProtectedStateImperativeTypedSourceSites.Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop items condition post statements)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (executed : Dynamic.ForItemsExecute program context evidence source environment before
      items loopContext next after)
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax loopContext
      (.initializers [] condition post statements) expected) :
    LoopFacts source expressionSyntax loopContext condition post statements expected := by
  obtain ⟨control, staticContext, postContext, bodyFinal, bodyFacts,
    itemsTyped, _conditionTyped, bodyTyped, postTyped⟩ :=
    ProtectedStateImperativeTypedSourceSites.for_loop unique parent found form
  have same := (executed.preserved wellFormed runtime covers locals heapTyped itemsTyped).1
  subst loopContext
  exact of_done syntaxTree bodyTyped postTyped

theorem sites {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (facts : LoopFacts source expressionSyntax context condition post statements expected)
    (found : source.lookupExpression? condition = some conditionNode) :
    ProtectedStateLexicalSourceSites.ExpressionFacts source context condition conditionNode ∧
      ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax context false statements expected := by
  obtain ⟨control, bodyFinal, bodyFacts, _postFinal, typed, bodySyntax, bodyTyped, _postTyped, _postSyntax⟩ := facts
  obtain ⟨original, contains, sameType⟩ := typed.stored_type
  have sameNode : original = conditionNode :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst original
  exact ⟨by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using typed,
    bodySyntax, control.enterLoop, bodyFinal, bodyFacts, bodyTyped⟩

end LoopFacts

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (guard : Location → NativeFrame → Prop)
  {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word} {scope : Scope}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport callerProtocol)

include transport in
theorem loop_preserves_bounded_for [FunctionCalls.FaultTokens faults] (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (loopFacts : LoopFacts source expressionSyntax context condition post statements expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostFaultsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      functions program evidence validity size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type
      (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  obtain ⟨conditionFacts, bodyFacts⟩ := LoopFacts.sites unique loopFacts conditionFound
  exact ProtectedFor.Body.Stateful.WithReady.loop_preserves_bounded_for
    functions program evidence callerProtocol guard transport
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedForReadiness.activation bridge)
    validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning child smaller))
    conditionFound conditionFacts bodyFacts conditionTree typed unique correct postPreserves postFaults

include transport in
/-- The exact same-code body compiler Tree supplies its existing control
shape proof, while the actual post-item producers keep their live states. -/
theorem loop_reflects_bounded_from_tree_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (loopFacts : LoopFacts source expressionSyntax context condition post statements expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostReflectsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (bodyTree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values source
      expressionSyntax certificates ambient.definitions administrative context scope
      (.statements false statements) expected type code) :
    ∀ size, size ≤ budget → ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      functions program evidence validity size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type
      (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  obtain ⟨conditionFacts, bodyFacts⟩ := LoopFacts.sites unique loopFacts conditionFound
  exact ProtectedFor.Body.Stateful.WithReady.loop_reflects_bounded_for
    functions program evidence callerProtocol guard transport
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedForReadiness.activation bridge)
    validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning child smaller))
    conditionFound conditionFacts bodyFacts conditionTree typed correct
    (fun executed => bodyTree.control_not_fault unique executed) postReflects

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads
/-! Bare assignment heads consume the actual operand token law and admitted
RHS children at their real snapshot. The original lower cores retain the same
fault or written prefix, returned rows and strict native continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
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
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (payloadModel checked registry functions) context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CompatibleBareAssignment.RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ProtectedBareAssignment.rhs_of_expression snapshot callerProtocol initial trace.sound ?_ represented
      finalHeaps maps worlds frame metadata ⟨reached, related⟩⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

private theorem rhs_reflects_at (size : Nat)
    (meaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (payloadModel checked registry functions) context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      CompatibleBareAssignment.RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, _post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    ProtectedBareAssignment.rhs_of_expression snapshot callerProtocol initial trace.sound evaluated.sound represented
      finalHeaps maps worlds frame metadata ⟨reached, related⟩⟩
end Rhs

section Heads
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
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

include observations extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_fault_with_operands [FunctionCalls.FaultTokens faults] (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
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
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, reached, related⟩ :=
      ProtectedBareAssignment.Stateful.preserves_fault_reachable_bounded_with_rhs callerProtocol budget initial layout empty extension
        (fun snapshot child smaller {_ _} childTrace => rhs_preserves_at bridge snapshot child (boundedMeaning child smaller)
          right found sourceTyped environments heaps locals agrees actualTyped initial admitted childTrace)
        observations right found rightView rightType profile environments heaps locals agrees actualTyped slot writable trace bounded next output invalid operands
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩

include observations transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped wellFormed runtime covers bare in
theorem reflects_with_operands [FunctionCalls.FaultTokens faults] (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge (payloadModel values.checked registry functions)
        context evidence source certificate faults size)) (operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    CallableIndexedOwnedAdmittedBareAssignmentHeads.ResultAt bridge size values.checked registry functions context evidence source faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedBareAssignment.Stateful.reflects_reachable_bounded_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted evaluated)
      observations right found rightView rightType profile environments heaps locals agrees actualTyped slot writable operands completed bounded
    cases result with
    | fault trace same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .fault trace same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success trace _ finalHeaps maps worlds preservation metadata count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success trace finalHeaps maps worlds preservation metadata count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related (CallableIndexedOwnedAssignmentAdmission.after_assignment_sized bridge context
          initial reached admitted wellFormed runtime covers locals assignmentTyped trace preservation) strict remaining
end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseBareAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPointwiseProjectedAssignmentHeads
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
theorem preserves_fault_with_diagnostics [FunctionCalls.FaultTokens faults] (budget : Nat)
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
theorem reflects_with_diagnostics [FunctionCalls.FaultTokens faults] (budget : Nat)
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
end
