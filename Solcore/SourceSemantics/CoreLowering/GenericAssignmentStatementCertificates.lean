import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates

/-! Assignment certificates follow the successful production place callback
and flow branch. Independent source typing and native site typing remain
explicit static inputs; no child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CompatibleEncoding (bind_ok)
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

private theorem stored_type {source : TypedSource} {context : SourceSemantics.Context} {rhs : ExpressionId}
    {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : ExpressionHasType source context rhs type) : node.type = type := by
  obtain ⟨actual, contains, same⟩ := typed.stored_type
  have identical := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
  exact identical ▸ same

/-- The bare path compiles only its RHS. Its receipt therefore requires no
certificate for unrelated source occurrences or nonexistent key computations. -/
theorem Head.of_lower_bare_with_token {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (unique : NodeOccurrencesUnique source)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ lowered, expression fuel source scope rhs reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? rhs = some node ∧ certificate scope rhs lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, prepared, index, lowered, binding, rootType, rawView, slot, layout, generated, sameType, _, codeEq⟩ :=
    CompatibleBareAssignment.of_lower bare accepted
  obtain ⟨node, found, tree⟩ := extract lowered generated
  have rawType := stored_type unique found rightTyped
  refine ⟨⟨prepared, index, [], prepared.route.rootSourceType, lowered, node, invalidOperand,
    .bare bare layout, slot, rootType ▸ writable binder binding, found, tree,
    by simpa only [rawType] using rawView, sameType, ?_⟩, codeEq, rfl⟩
  rcases profile with equal | word | integer
  · exact .inl equal
  · exact .inr (.inl (rawView.trans word))
  · exact .inr (.inr (rawView.trans integer))

/-- Compatibility projection of the actual compiler receipt. -/
theorem Head.of_lower_bare {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (unique : NodeOccurrencesUnique source)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ lowered, expression fuel source scope rhs reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? rhs = some node ∧ certificate scope rhs lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := Head.of_lower_bare_with_token bare unique writable rightTyped profile extract accepted
  exact ⟨head, emitted⟩

/-- Only actual ordered key occurrences are requested from the expression
extractor. Repeated occurrences retain their repeated compiler receipts. -/
private theorem keys_of_generated {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {expression : ExpressionLowerer} {fuel : Nat} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (generated : ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes)
    (extract : ∀ id code, id ∈ DataPlaceKeyOrder.sourceKeys projections → expression fuel source scope id reasonAt = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes ∧
      keys.map Prod.snd = codes.map (·.type) := by
  have collect : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
      (∀ id code, id ∈ keys.map Prod.fst → expression fuel source scope id reasonAt = .ok code →
        ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => intro _; exact ⟨.nil, rfl⟩
    | cons head tail ih =>
      intro extract
      have rest := ih (fun id code member compiled => extract id code (List.mem_cons_of_mem _ member) compiled)
      exact ⟨.cons (extract _ _ (by simp) head.1) rest.1, by simp only [List.map_cons, head.2, rest.2]⟩
  have receipts := collect generated (fun id code member compiled => extract id code (by simpa only [PreparedPath.key_ids path] using member) compiled)
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [PreparedPath.key_ids path] at tree
  exact ⟨types, tree, receipts.2⟩

theorem Head.of_lower_with_token {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
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
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  classical
  by_cases bare : assignment.target.projections = []
  · apply Head.of_lower_bare_with_token bare unique writable rightTyped profile ?_ accepted
    intro lowered generated
    obtain ⟨node, found, tree, _⟩ := extract rhs lowered (by simp) generated
    exact ⟨node, found, tree⟩
  · cases generated_of_lower accepted with
    | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
      cases rhsGenerated with
      | @present id right rhsGenerated rhsType =>
        obtain ⟨node, found, certified, rhsTyped⟩ := extract rhs right (by simp) rhsGenerated
        obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
        obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
        obtain ⟨sourceTypes, tree, keyTypes⟩ := keys_of_generated path generated
          (fun id code member compiled => let ⟨node, found, certified, _⟩ := extract id code (List.mem_cons_of_mem rhs member) compiled; ⟨node, found, certified⟩)
        obtain ⟨views, leafView⟩ := CompatiblePlaceKeyTyping.of_typing unique signatures path rfl (sourceTyped binder description.binding) tree
        have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
        have actualPath : PreparedPath values.checked source site prepared.route.rootSourceType assignment.target.projections
            0 prepared.steps prepared.keys leaf := rootEq ▸ path
        have rhsType : right.type = prepared.route.leafType := by simpa only [routeEq] using rhsType.symm
        have layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
            assignment.target prepared codes sourceTypes leaf administrative := by
          refine ⟨actualPath, by simpa only [rootEq] using views, tree, keyTypes, ?_, ?_, ?_,
            CompatiblePlaceHelperTyping.getter_of_execute typed,
            CompatiblePlaceHelperTyping.setter_of_execute typed (CompatiblePlaceHelperTyping.rhs_shift_typed (by simpa only [rhsType] using rhsTyped))⟩
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
          found, certified, by simpa only [rawType] using leafView, rhsType, ?_⟩, by simp [Head.emit, routeEq], rfl⟩
        rcases profile with equal | word | integer
        · exact .inl equal
        · exact .inr (.inl (leafView.trans word))
        · exact .inr (.inr (leafView.trans integer))

/-- Compatibility projection of the actual compiler receipt. -/
theorem Head.of_lower {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
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
      expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := Head.of_lower_with_token unique signatures sourceTyped writable rightTyped profile extract accepted typed
  exact ⟨head, emitted⟩

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
