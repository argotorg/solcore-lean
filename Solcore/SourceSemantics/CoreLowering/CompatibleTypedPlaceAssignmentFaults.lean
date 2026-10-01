import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceFailures
import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceStructuralFault

/-! Every independently specified assignment fault in the nonempty equal or
numeric profile is preserved. Unbound/dangling roots contradict actual lexical
and heap agreement. Invalid operands contradict the represented snapshot and
RHS values; neither exclusion is inferred from native type equality alone. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, sourceCell, sourceLookup, sourceRead, _, _⟩ := locals.lookup staticLookup
  cases trace with
  | target fault =>
    cases fault with
    | unbound missing => exact (missing.excludes_lookup sourceLookup).elim
    | dangling lookup missing =>
      have same := lookup.functional sourceLookup
      cases same
      exact (missing.excludes_read sourceRead).elim
    | projectionExpression lookup read fault =>
      obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceFailures.keys layout.children meaning environments heaps locals slot lookup read fault
          operator rhs lowered.expression next outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | danglingAfterProjections lookup read evaluated missing =>
      obtain ⟨keys⟩ := CompatibleTypedPlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup read evaluated
      exact (missing.excludes_read keys.read).elim
    | projectionRead lookup initialRead evaluate currentRead initialValue fault =>
      obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceTargetFaults.projection layout meaning environments heaps locals slot rootTyped lookup initialRead evaluate currentRead
          registryExtension faithful observations initialValue fault operator rhs lowered.expression next outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩
    | uninitialized lookup initialRead evaluate currentRead empty notMapping projected =>
      obtain ⟨finalStore, finalMap, finalWorld, _, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceTargetFaults.uninitialized layout meaning environments heaps locals slot rootTyped lookup initialRead evaluate currentRead
          ordinary empty notMapping projected operator rhs lowered.expression next outputType invalid
      exact ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, evaluated, invalidTokens _, finalHeaps, maps, worlds, frame, metadata⟩
  | rhs resolve fault =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleTypedPlaceFailures.rhs resolution meaning rhsGenerated found rhsCoreType environments locals resolve coreLookup fault
        operator next outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  | operands resolve evaluate _ _ _ _ invalidOperands =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatibleTypedPlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf _ rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
      obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceModifier.initialized_success observations operatorProfile
        rhsResult.saved_snapshot rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
  | structuralUpdate resolve evaluate currentRead sameType initialValue fault =>
    obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleTypedPlaceStructuralFault.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals slot rootTyped resolve evaluate currentRead sameType initialValue fault next outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
