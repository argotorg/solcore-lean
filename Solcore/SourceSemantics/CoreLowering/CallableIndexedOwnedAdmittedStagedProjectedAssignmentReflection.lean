import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads

/-! Native projected writes reconstruct the ordered staged key row and RHS
at their actual reached states. Only successful children are erased for the
existing pure setter; staged faults retain their own tag and endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
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
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyRow : ExpressionsHaveTypes invocation.source context
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) sourceTypes := by
      simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using tree_typed layout.children unique keyTyped
    have nativeCompleted := completed
    change EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next output
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore at nativeCompleted
    rw [execute_rename layout.path (virtual_closed layout ordinary)] at nativeCompleted
    simp only [renamed_packed, Expr.rename] at nativeCompleted
    have prefixResult := ProtectedStagedProjectedPrefix.reflects_getter budget layout ordinary extension
      callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial missing uninitialized
      (by
        intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
            frame, metadata, typedValues, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.reflects bridge budget layout.children unique keyTyped
            boundedReflection environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted evaluated smaller
        refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
          frame, metadata, ?_, reached, related⟩
        · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
        · intro sources same
          exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
      slot writable nativeCompleted bounded
    cases prefixResult with
    | keyFault ready trace same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .keyFault ready trace same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | getterFault trace failed same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .getterFault trace failed same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | resolved resolution keyTrace snapshot keyValues getterHeap prefixBound remaining prefixPost =>
      obtain ⟨getterState, getterRelated⟩ := prefixPost
      have getterAdmission : Admission bridge context getterState :=
        ⟨getterHeap, StableRows.after_administrative (bridge.pool initial) (bridge.pool getterState) admitted.rows resolution.frame⟩
      have reflectRhs := fun {child : Nat} {value : Value} {finalStore : Store}
          (evaluated : EvaluationSize child
            (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) actual) resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore)
          (smaller : child < budget) =>
        rhs_reflects_at bridge resolution child (boundedReflection child smaller) generated found sourceTyped
          (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
          agrees actualTyped getterState getterAdmission evaluated
      cases remaining with
      | caseLeft evaluated failed =>
        obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
        cases represented : result.represented with
        | fault matched =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var foundValue =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at foundValue
              subst_vars
              obtain ⟨reached, related⟩ := rhsPost
              exact .rhsFault keyTrace snapshot result.trace rfl matched result.heaps
                (resolution.maps.trans result.maps) (resolution.worlds.trans result.worlds)
                (resolution.frame.trans result.frame) (resolution.metadata.trans result.metadata) reached
                (callerProtocol.trans getterRelated related)
                (StableRows.after_administrative (bridge.pool getterState) (bridge.pool reached) getterAdmission.rows result.frame)
      | caseRight evaluated continuation =>
        rename_i rhsStore rightValue
        obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
        cases represented : result.represented with
        | @value right _ payload =>
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          obtain ⟨rightTyped, middleTyped⟩ := result.sourcePost _ rfl
          obtain ⟨plainRhs, _⟩ := ProtectedPlaceRhs.rhs_of_expression resolution callerProtocol getterState
            (faults := fun reason token => faults (.semantic reason) token)
            (.value result.trace.sound.value_plain) result.evaluated (.value payload)
            result.heaps result.maps result.worlds result.frame result.metadata ⟨rhsState, rhsRelated⟩
          have rightRep : CompatiblePayload.ValueRep values.checked registry functions finalMap finalWorld leaf right rightValue prepared.route.leafType :=
            .compatible rightView (by simpa only [payloadModel, rightType] using payload)
          let rightExecution : CompatiblePlaceRhsReflection.Execution values.checked registry functions program context
              invocation.evidence invocation.source (fun reason token => faults (.semantic reason) token) environment
              prepared (renamedCodes codes ξ) sourceTypes assignment.target leaf _ actual store mapping world before _
              resolution rhs node (renamed lowered ξ) :=
            ⟨right, rightValue, after, _, finalMap, finalWorld, plainRhs, rightRep⟩
          obtain ⟨resolveSize, resolve⟩ := SourceExecutionSize.SourcePlaceResolves.has_size
            (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace))
          obtain ⟨plainRhsSize, plainRhsTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size result.trace.sound.value_plain
          simp only [packed_renamed_type] at continuation
          have tail := ProtectedStagedProjectedTail.reflects callerProtocol transport layout ordinary extension functionTypes faithful observations
            profile environments agrees actualTyped resolve resolution rightExecution plainRhsTrace initial rhsState
            (callerProtocol.trans getterRelated rhsRelated) missing continuation
          cases tail with
          | fault failed same matched finalHeaps maps worlds frame metadata post =>
            obtain ⟨reached, related⟩ := post
            exact .writeFault keyTrace snapshot result.trace failed same matched finalHeaps maps worlds frame metadata reached related
              (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
          | committed write finalHeaps maps worlds frame metadata count typed post strict continuation =>
            obtain ⟨reached, related⟩ := post
            exact .success keyTrace snapshot result.trace write finalHeaps maps worlds frame metadata count
              (by simpa only [GenericAssignmentStatements.Head.writtenContext] using typed)
              reached related
              ⟨CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped locals
                keyRow keyValues getterHeap resolution.metadata snapshot middleTyped rightTyped result.metadata write,
                StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
              (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
