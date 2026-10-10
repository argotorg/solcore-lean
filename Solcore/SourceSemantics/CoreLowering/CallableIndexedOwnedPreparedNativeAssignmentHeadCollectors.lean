import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren

/-! Actual compatible lowering and its enclosing native typing manufacture
all local RHS/key witnesses for the static expression factory. The original
Source typing, writable route, prepared layout, full node identity and exact
assignment token remain independent. No expected child typing or expression
execution is supplied by a callback. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates
open GenericAssignmentStatements CallableIndexedOwnedPreparedNativeAssignmentChildren

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

/-- The same real Head.PreparedAt is produced with the original layout.
The expression factory receives the actual raw Core witness at this Source
occurrence, from this lowering, scope, context and compiler fuel. -/
theorem Head.of_lower_with_raw_occurrences {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered →
      RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression definitions →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand ∧
        head.PreparedAt site fuel invalidProjection missing := by
  classical
  by_cases bare : assignment.target.projections = []
  · obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
    have rhsNative := execute_present_rhs (prepared := prepared) (reference := .var index)
      (keys := SourceCoreCalls.packArguments []) (rhs := value.expression) (next := next)
      (output := output) (result := result) (operator := operator) (codeEq ▸ typed)
    obtain ⟨head, emitted, token⟩ := Head.of_lower_bare_with_token bare unique writable rightTyped profile
      (fun lowered acceptedRight => by
        have same : lowered = value := Except.ok.inj (acceptedRight.symm.trans generated)
        subst lowered
        exact extract rhs value (by simp) generated ⟨_, rhsNative⟩) accepted
    exact ⟨head, emitted, token, .bare bare⟩
  · cases generated_of_lower accepted with
    | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
      cases rhsGenerated with
      | @present id right rhsGenerated rhsType =>
        obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
        obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
        have rhsNative := execute_present_rhs (prepared := prepared) (reference := .var index)
          (keys := SourceCoreCalls.packArguments codes) (rhs := right.expression) (next := next)
          (output := output) (result := result) (operator := operator)
          (by simpa only [routeEq, Option.isNone_some] using typed)
        obtain ⟨node, found, certified⟩ := extract rhs right (by simp) rhsGenerated ⟨_, rhsNative⟩
        obtain ⟨_rhsRaw, ⟨packedResult, packedNative⟩⟩ := execute_children typed
        obtain ⟨sourceTypes, tree, keyTypes⟩ :=
          CallableIndexedOwnedPreparedNativeAssignmentChildren.keys_of_generated path generated packedNative
            (fun id code member compiled raw => extract id code (List.mem_cons_of_mem rhs member) compiled raw)
        obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
        have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
        have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
            0 prepared.steps prepared.keys leaf := rootEq ▸ path
        have rhsType : right.type = prepared.route.leafType := by simpa only [routeEq] using rhsType.symm
        have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
            assignment.target prepared codes sourceTypes leaf administrative := by
          refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
            CompatiblePlaceHelperTyping.getter_of_execute typed,
            CompatiblePlaceHelperTyping.setter_of_execute typed (CompatiblePlaceHelperTyping.rhs_shift_typed (by simpa only [rhsType] using rhsNative))⟩
          · rw [← values.checked.catalog.project_runtimeType leaf, description.selectedType,
              values.checked.catalog.project_runtimeType, routeEq]
            exact description.leafProjected
          · intro k v declared
            rw [routeEq]
            exact description.virtual k v (rootEq.symm.trans declared)
          · intro empty
            have length := PreparedPath.steps_length path
            rw [empty, List.length_nil] at length
            exact bare (List.eq_nil_of_length_eq_zero length.symm)
        have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
          intro notMapping
          rw [routeEq]
          exact description.ordinary (fun k v same => notMapping k v (rootEq.trans same))
        have rawType := stored_type unique found rightTyped
        refine ⟨⟨prepared, index, codes, leaf, right, node, invalidOperand,
          .projected layout ordinary, by simpa only [routeEq] using lookup, rootEq ▸ writable binder description.binding,
          found, certified, by simpa only [rawType] using leafView, rhsType, ?_⟩, by simp [Head.emit, routeEq], rfl, ?_⟩
        · rcases profile with equal | word | integer
          · exact .inl equal
          · exact .inr (.inl (leafView.trans word))
          · exact .inr (.inr (leafView.trans integer))
        · exact .projected route layout ordinary rfl described preparedBy

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
