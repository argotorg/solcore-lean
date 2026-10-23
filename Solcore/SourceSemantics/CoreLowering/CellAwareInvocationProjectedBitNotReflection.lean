import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotPreservation
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateProjectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedPrefix

/-! Completed native unary writes reconstruct the staged key row and saved snapshot.
The typed numeric snapshot supplies the actual independent Source write. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)

include transport extension environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) functions callerProtocol head environment initial (fun reason token => faults (.semantic reason) token) (registry := registry))
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) context stages invocation faults
      scope (head.writtenContext actualContext) assignment environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  have _nonempty := projected
  cases assignmentTyped with
  | intro targetTyped word =>
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyRow : ExpressionsHaveTypes invocation.source context
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) head.sourceTypes := by
      simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using CellAwareInvocationProjectedAssignmentHeads.tree_typed head.layout.children unique keyTyped
    have nativeCompleted := completed
    change EvaluationSize size actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit) next output
        (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) value finalStore at nativeCompleted
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)] at nativeCompleted
    simp only [renamed_packed, Expr.rename, LanguageResult.success] at nativeCompleted
    have prefixResult := CellAwareStagedProjectedPrefix.reflects_getter budget GeneralizedLocalDescriptorHeap.ordinary_cells head.layout head.ordinary extension
      callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial errors.missing errors.uninitialized
      (by
        intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
            frame, metadata, effect, typedValues, reached, related, post⟩ :=
          CellAwareInvocationTypedExpressionSequence.reflects bridge budget head.layout.children unique keyTyped
            boundedReflection environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType head.prepared.route.rootType) target])
            hiddenTyped initial admitted authority physical owner ownerFrame evaluated smaller
        refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
          frame, metadata, effect, ?_, reached, related⟩
        · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
        · intro sources same
          exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
      head.slot head.writable nativeCompleted bounded
    cases prefixResult with
    | keyFault ready trace same matched finalHeaps maps worlds frame metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .keyFault ready trace same matched finalHeaps maps worlds frame metadata effect reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | getterFault trace failed same matched finalHeaps maps worlds frame metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .getterFault trace failed same matched finalHeaps maps worlds frame metadata effect reached related
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
        CellAwareStagedProjectedBitNotCommit.of_write GeneralizedLocalDescriptorHeap.ordinary_cells head.layout head.ordinary extension callerProtocol transport faithful observations
          head.profile environments agrees actualTyped resolution initial getterState getterRelated write
          (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
      obtain ⟨remainingSize, strict, continuation⟩ := commit.reflects_size remaining
      exact .success keyTrace snapshot write commit.heaps resolution.maps
        (resolution.worlds.trans commit.worlds) (resolution.frame.trans commit.frame)
        (resolution.metadata.trans commit.metadata)
        (resolution.effect.trans commit.effect)
        (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
          packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target])
        rfl typed reached related
        ⟨CallableIndexedOwnedStagedProjectedBitNotAdmission.heap_after_bitNot unique (.intro targetTyped word)
          locals keyRow keyValues getterHeap resolution.metadata snapshot write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows
            (resolution.frame.trans commit.frame)⟩
        (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedBitNotHeads
