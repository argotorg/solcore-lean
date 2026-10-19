import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
import Solcore.SourceSemantics.CoreLowering.GenericProjectedBitNotPreparedOrigins

/-! Actual native typing supplies each ordered key witness. The absent RHS
remains a literal Unit and never becomes a Source expression certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates
open CompatibleProjectedBitNotStatements CallableIndexedOwnedPreparedNativeAssignmentChildren

theorem Head.of_lower_with_raw_occurrences {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidUnary : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (projected : assignment.target.projections ≠ [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered →
      RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression definitions →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalidProjection invalidUnary missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment,
      code = head.emit next output ∧ head.invalid = invalidUnary ∧
        head.PreparedAt site fuel invalidProjection missing := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      obtain ⟨_rhsRaw, ⟨packedResult, packedNative⟩⟩ := execute_children typed
      obtain ⟨sourceTypes, tree, keyTypes⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentChildren.keys_of_generated path generated packedNative extract
      obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl
        (sourceTyped binder description.binding) tree
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
          0 prepared.steps prepared.keys leaf := rootEq ▸ path
      have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
          assignment.target prepared codes sourceTypes leaf administrative .unit := by
        refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
          CompatiblePlaceHelperTyping.getter_of_execute typed,
          CompatiblePlaceHelperTyping.setter_of_execute_rhs typed
            (CompatiblePlaceHelperTyping.rhs_shift_typed_rhs (LanguageResult.success_hasType .unit))⟩
        · rw [← values.checked.catalog.project_runtimeType leaf, description.selectedType,
            values.checked.catalog.project_runtimeType, routeEq]
          exact description.leafProjected
        · intro k v declared
          rw [routeEq]
          exact description.virtual k v (rootEq.symm.trans declared)
        · intro empty
          have length := PreparedPath.steps_length path
          rw [empty, List.length_nil] at length
          exact projected (List.eq_nil_of_length_eq_zero length.symm)
      have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
        intro notMapping
        rw [routeEq]
        exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))
      refine ⟨⟨prepared, index, codes, leaf, sourceTypes, site, invalidUnary, layout, ordinary,
        by simpa only [routeEq] using lookup, rootEq ▸ writable binder description.binding, leafView ▸ profile⟩,
        by simp [Head.emit, routeEq], rfl, ?_⟩
      exact ⟨rfl, route, described, preparedBy⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
