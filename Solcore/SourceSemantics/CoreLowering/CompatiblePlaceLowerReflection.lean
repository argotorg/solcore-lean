import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates

/-! The production compatible place lowerer is connected to whole assignment
reflection. Only universal child typing/meaning and independent checked source
facts remain; no manually supplied path or helper-typing layout is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {rhs : ExpressionId} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType resultType : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code.expression (LanguageResult.resultType code.type)
        ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs) outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType ambient.definitions)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {prepared root resolved reason token count},
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) →
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) invalid)
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceTailReflection.Result compilation.checked registry functions program context evidence source faults assignment.target operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, right, node, actualPreparation, binding, rootEq, slot, layout, ordinary,
      generated, found, certified, rhsView, rhsType, lowering⟩ :=
    CompatiblePlaceLayoutCertificates.of_lower unique signatures sourceTyped rightTyped nonempty extract accepted typed
  obtain ⟨typedNode, contains, nodeType⟩ := rightTyped.stored_type
  have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  have leafView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type := by
    simpa only [same, nodeType] using rhsView
  have profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer := by
    simpa only [leafView] using operatorProfile
  have invalidEq : prepared.invalidProjection = invalid := by
    obtain ⟨route, _, preparedBy⟩ := actualPreparation
    exact (CompatibleMixedPreparation.of_prepare preparedBy).2.1
  exact CompatiblePlaceAssignmentReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    (fun receipt => missingTokens actualPreparation receipt) (by simpa only [invalidEq] using invalidTokens)
    certified found rhsView rhsType profile environments heaps locals slot (rootEq ▸ rootTyped binder binding) (lowering ▸ completed)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection
