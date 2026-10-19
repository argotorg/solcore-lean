import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentPreservation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open SourceCoreCompatibleDataPlaces
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context} {receiving : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry receiving)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr}
  {rhsType : Core.Ty} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty} {administrative : Core.Context}

local notation "model" => CompatibleAmbientHeap.payloadModel values.checked receiving functions

include extension transport faithful observations in
/-- Ordinary key effects are lifted before the getter and before any RHS. -/
theorem lifts (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (keyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model stages invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before after : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
    {index : Nat} {target : Dynamic.ResolvedPlace} {size : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : SourceExecutionSize.SourcePlaceResolves program size context invocation.evidence invocation.source
      environment before place target after) (within : size ≤ budget) :
    (∃ origin call reason reached,
      Staging.Recursive.ProjectedTarget.RootReady environment before place ∧
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.fault (.stage origin call reason)) reached) ∨
    (∃ sources,
      Staging.Recursive.Expressions program stages invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) after ∧
      Staging.Recursive.ProjectedTarget.Snapshot environment before after place sources target ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ resolution : CompatiblePlaceResolution.Execution values.checked receiving functions prepared
        (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before after,
        ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, after, resolution.store, canonical⟩,
          callerProtocol.Relates initial reached ∧ Admission bridge context reached) := by
  obtain ⟨keySize, sources, keyBound, ordinaryKeys, snapshot⟩ := SelectedCompilationStageProjectedTargetInversion.resolved trace
  have rowTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed layout.children unique keyTyped
  obtain ⟨outcome, reached, stagedKeys, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
    layout.children unique rowTyped children preservation environments heaps locals agrees actualTyped initial admitted
    (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
    (Nat.le_trans (Nat.le_of_lt keyBound) within)
  have keyTrace : Staging.Recursive.Expressions program stages invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) outcome reached := by
    simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using stagedKeys
  cases adapted with
  | rejected origin call reason reached =>
      refine .inl ⟨origin, call, reason, reached, ?_, keyTrace⟩
      cases snapshot with
      | intro lookup read _ _ _ _ => exact .intro lookup read
  | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expressions.of_trace keyTrace
      obtain ⟨resolution, _sameSources, keyValues, _keyHeap, _lookup, reached, related, admitted⟩ :=
        CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_resolution bridge stagedSize layout ordinary
          extension transport faithful observations environments heaps locals agrees actualTyped initial admitted unique
          keyTyped (fun n _ => preservation n) slot writable measured (Nat.le_refl _) snapshot
      exact .inr ⟨sources, keyTrace, snapshot, keyValues, resolution, reached, related, admitted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
