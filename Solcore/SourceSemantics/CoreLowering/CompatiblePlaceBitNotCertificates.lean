import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates

/-! The actual absent-RHS branch retains a literal Unit administrative slot.
Only index children receive source expression certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

theorem of_describe_prepare {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route} {prepared : Prepared}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    {administrativeContext : Core.Context} {reference rhs next : Expr} {outputType resultType : Ty}
    {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (described : describe compilation compilation.checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation fuel route invalid missing = .ok prepared)
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext)
      (execute prepared reference (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalidOperand)
      resultType compilation.checked.catalog.definitions)
    (rhsTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) rhs
      (LanguageResult.resultType .unit) compilation.checked.catalog.definitions) :
    ∃ binder leaf sourceTypes,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext .unit ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) := by
  obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  obtain ⟨sourceTypes, tree, keyTypes⟩ := tree_of_keys path generated extract
  obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
  have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
  have actualPath : PreparedPath compilation.checked source site prepared.route.rootSourceType assignment.target.projections
      0 prepared.steps prepared.keys leaf := rootEq ▸ path
  refine ⟨binder, leaf, sourceTypes, description.binding, rootEq, leafView, ?_, ?_⟩
  · refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
      CompatiblePlaceHelperTyping.getter_of_execute typed,
      CompatiblePlaceHelperTyping.setter_of_execute_rhs typed (CompatiblePlaceHelperTyping.rhs_shift_typed_rhs rhsTyped)⟩
    · rw [← compilation.checked.catalog.project_runtimeType leaf, description.selectedType,
        compilation.checked.catalog.project_runtimeType, routeEq]
      exact description.leafProjected
    · intro k v declared
      rw [routeEq]
      exact description.virtual k v (rootEq.symm.trans declared)
    · intro empty
      have length := PreparedPath.steps_length path
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
  · intro notMapping
    rw [routeEq]
    exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))

/-- Actual `rhs := none` compilation fixes the Unit RHS, with no source
expression invented for that administrative value. -/
theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope}
    {reasonAt : ExpressionId → Word} {operator : Syntax.ValueAssignOp}
    {next lowered : Expr} {outputType resultType : Ty} {invalid invalidOperand : Word}
    {missing : TypeSystem.Ty → Word} {certificate : GenericExpressionMeaning.Certificate} {administrativeContext : Core.Context}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none outputType
      next reasonAt invalid invalidOperand missing = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) lowered resultType compilation.checked.catalog.definitions) :
    ∃ binder leaf prepared codes sourceTypes index,
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) ∧
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site assignment.target prepared codes sourceTypes leaf administrativeContext .unit ∧
      ((∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none) ∧
      (prepared.route.leafType = .word ∨ prepared.route.leafType = .integer) ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments codes) (LanguageResult.success .unit) next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand := by
  have receipt := CompatiblePlaceCompilerCertificates.generated_of_lower accepted
  cases receipt with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      have routeEq := (CompatibleMixedPreparation.of_prepare preparedBy).1
      obtain ⟨binder, leaf, sourceTypes, binding, rootEq, leafView, layout, ordinary⟩ :=
        of_describe_prepare unique signatures sourceTyped nonempty described preparedBy generated extract typed
          (LanguageResult.success_hasType .unit)
      have profile : prepared.route.leafType = .word ∨ prepared.route.leafType = .integer := by
        simpa only [Option.isNone_none, Bool.true_eq_false, and_false, false_or, routeEq] using operatorValid
      exact ⟨binder, leaf, prepared, codes, sourceTypes, index, ⟨route, described, preparedBy⟩, binding, rootEq,
        leafView, by simpa only [routeEq] using lookup, layout, ordinary, profile, by simp [routeEq]⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotCertificates
