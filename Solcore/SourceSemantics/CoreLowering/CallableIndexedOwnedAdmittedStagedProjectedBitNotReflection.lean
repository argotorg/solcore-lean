import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads

/-! Completed native unary writes reconstruct the staged key row and saved snapshot.
The typed numeric snapshot supplies the actual independent Source write. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
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
  {assignment : AssignmentResolution}
  (head : CompatibleProjectedBitNotStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment)
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
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : head.ReachedErrors functions callerProtocol environment initial (fun reason token => faults (.semantic reason) token) (registry := registry))
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped word =>
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyRow : ExpressionsHaveTypes invocation.source context
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) head.sourceTypes := by
      simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed head.layout.children unique keyTyped
    have nativeCompleted := completed
    change EvaluationSize size actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit) next output
        (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) value finalStore at nativeCompleted
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)] at nativeCompleted
    simp only [renamed_packed, Expr.rename, LanguageResult.success] at nativeCompleted
    have prefixResult := ProtectedStagedProjectedPrefix.reflects_getter budget head.layout head.ordinary extension
      callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial errors.missing errors.uninitialized
      (by
        intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
            frame, metadata, typedValues, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.reflects bridge budget head.layout.children unique keyTyped
            boundedReflection environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType head.prepared.route.rootType) target])
            hiddenTyped initial admitted evaluated smaller
        refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
          frame, metadata, ?_, reached, related⟩
        · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
        · intro sources same
          exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
      head.slot head.writable nativeCompleted bounded
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
      obtain ⟨replacement, native, represented, applies, _, _⟩ :=
        CompatiblePlaceNumericBitNotModifier.success head.profile resolution.snapshotRelated
          (environment := rhsEnvironment head.prepared.route.rootType resolution.target (packValues resolution.values)
            (.inRight .unit resolution.snapshot) .unit actual) (rhs := .var 0) (.var (index := 1) rfl)
          (binaryOperator (head.prepared.route.leafType = .integer) .equal) resolution.store head.invalid
      have applies := resolution.selectedEq.symm ▸ applies
      have sourceTrace := snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)
      obtain ⟨updated, after, write⟩ := CompatiblePlaceBitNotModifier.write_exists sourceTrace applies
      obtain ⟨commit, typed, reached, related⟩ :=
        ProtectedStagedProjectedBitNotCommit.of_write head.layout head.ordinary extension callerProtocol transport faithful observations
          head.profile environments agrees actualTyped resolution initial getterState getterRelated write
          (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
      obtain ⟨remainingSize, strict, continuation⟩ := commit.reflects_size remaining
      exact .success keyTrace snapshot write commit.heaps resolution.maps
        (resolution.worlds.trans commit.worlds) (resolution.frame.trans commit.frame)
        (resolution.metadata.trans commit.metadata)
        (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
          packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target])
        rfl typed reached related
        ⟨CallableIndexedOwnedStagedProjectedBitNotAdmission.heap_after_bitNot unique (.intro targetTyped word)
          locals keyRow keyValues getterHeap resolution.metadata snapshot write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows
            (resolution.frame.trans commit.frame)⟩
        (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads
