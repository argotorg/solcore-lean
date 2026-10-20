import Lean
import Solcore.SourceSemantics.SourcePreparedOpenCallEdges
import Solcore.SourceSemantics.SubstitutionProperties

/-! Qualified local references in a successfully prepared original source row
retain the exact existing matching and requirement checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
open Frontend SourceInference SourceSpecializationWorklist TypeSystem
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

/-- Unfold the actual checked computation without encoding an imported private
name. This only invokes Lean's ordinary kernel-checked unfolding tactic. -/
private def unfoldCheck (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some checkedDecl := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing checked call"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType checkedDecl.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality: {type}"
    let .const targetName _ := left.getAppFn | throwError "expected checked constant: {left}"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal checkedDecl.fvarId targetName
    Lean.Elab.Tactic.replaceMainGoal [updated]

private theorem forIn_append {α β ε : Type} {items : List α} {initial final : List β}
    {step : α → List β → Except ε (ForInStep (List β))}
    (project : β → α) (property : β → Prop)
    (accepted : forIn items initial step = .ok final)
    (each : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ value, outcome = .yield (before ++ [value]) ∧ project value = item ∧ property value) :
    final.map project = initial.map project ++ items ∧
      ∀ value ∈ final, value ∈ initial ∨ property value := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨by simp, fun _ member => .inl member⟩
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, remaining⟩ := bind_ok accepted
    obtain ⟨value, rfl, projected, checked⟩ := each item List.mem_cons_self initial outcome executed
    obtain ⟨mapped, properties⟩ := ih remaining (fun next present => each next (List.mem_cons_of_mem item present))
    refine ⟨?_, ?_⟩
    · simpa only [List.map_append, List.map_cons, List.map_nil, projected, List.append_assoc,
        List.singleton_append] using mapped
    · intro actual member
      rcases properties actual member with old | later
      · rcases List.mem_append.mp old with entering | added
        · exact .inl entering
        · cases List.mem_singleton.mp added
          exact .inr checked
      · exact .inr later

/-- Every row is the result of the actual ordered template/requirement loop.
Both solved-ledger lookups remain exact singleton selections. -/
structure CheckedBinding (caller : Specialized) (substitution : Substitution)
    (binding : SourceCompilationPlan.LocalRequirementBinding) : Prop where
  predicate : binding.predicate = (binding.template.applySubstitution substitution).predicate
  ground : (TypedTraitResolution.predicateVariables binding.predicate) = []
  template : ∃ row,
    caller.function.solvedRequirements.filter (fun candidate =>
      decide (candidate.id = binding.template.templateRequirement)) = [row] ∧
    row.predicate = binding.template.predicate ∧ row.evidence.goal = binding.template.predicate ∧
    ∃ assumption, row.evidence = .assumption assumption
  actual : caller.function.solvedRequirements.filter (fun candidate =>
    decide (candidate.id = binding.actualRequirement)) = [binding.actualSolved]
  actualPredicate : binding.actualSolved.predicate = binding.predicate
  actualGoal : binding.actualSolved.evidence.goal = binding.predicate

structure BindingsReceipt (caller : Specialized) (binder : TypedBinder) (node : ExpressionNode)
    (substitution : Substitution) (bindings : List SourceCompilationPlan.LocalRequirementBinding) : Prop where
  accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)
  matched : SourceSpecialization.matchClosedSchemeInstance? binder.scheme node.rawType = some substitution
  count : binder.schemeRequirements.length = node.requirements.length
  pairs : bindings.map (fun binding => (binding.template, binding.actualRequirement)) =
    binder.schemeRequirements.zip node.requirements
  checked : ∀ binding ∈ bindings, CheckedBinding caller substitution binding

theorem bindings_receipt {caller : Specialized} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)) :
    BindingsReceipt caller binder node substitution bindings := by
  have original := accepted
  unfold SourceCompilationPlan.localRequirementBindings at accepted
  simp (maxSteps := 1000000) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i matched matchedEq
  split at accepted <;> try contradiction
  rename_i countEq
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨final, loop, returned⟩ := bind_ok accepted
  cases returned
  have count : binder.schemeRequirements.length = node.requirements.length := by
    simpa using countEq
  have finished := forIn_append
    (fun binding : SourceCompilationPlan.LocalRequirementBinding =>
      (binding.template, binding.actualRequirement))
    (CheckedBinding caller substitution) loop (by
      intro pair _ before outcome iteration
      rcases pair with ⟨template, actual⟩
      dsimp only at iteration
      obtain ⟨templateSolved, templateSelected, iteration⟩ := bind_ok iteration
      have templateExact : (caller.function.solvedRequirements.filter fun candidate : SolvedRequirement =>
          decide (candidate.id = template.templateRequirement)) = [templateSolved] := by
        run_tac unfoldCheck `templateSelected
        dsimp only at templateSelected
        split at templateSelected <;> try contradiction
        rename_i sole selected
        cases templateSelected
        exact selected
      try dsimp only at iteration
      split at iteration <;> try contradiction
      rename_i templatePredicate
      split at iteration <;> try contradiction
      rename_i templateGoal
      split at iteration <;> try contradiction
      rename_i assumption assumptionEq
      split at iteration <;> try contradiction
      rename_i ground
      obtain ⟨actualSolved, actualSelected, iteration⟩ := bind_ok iteration
      have actualExact : (caller.function.solvedRequirements.filter fun candidate : SolvedRequirement =>
          decide (candidate.id = actual)) = [actualSolved] := by
        run_tac unfoldCheck `actualSelected
        dsimp only at actualSelected
        split at actualSelected <;> try contradiction
        rename_i sole selected
        cases actualSelected
        exact selected
      try dsimp only at iteration
      split at iteration <;> try contradiction
      rename_i actualPredicate
      split at iteration <;> try contradiction
      rename_i actualGoal
      cases iteration
      refine ⟨_, rfl, rfl, ?_⟩
      constructor
      · rfl
      · simpa using ground
      · refine ⟨templateSolved, templateExact, ?_, ?_, assumption, assumptionEq⟩
        · simpa using templatePredicate
        · simpa using templateGoal
      · exact actualExact
      · simpa using actualPredicate
      · simpa using actualGoal)
  exact ⟨original, matchedEq, count, by simpa using finished.1,
    fun binding member => (finished.2 binding member).resolve_left (by simp)⟩

private theorem metadata_aux {program : CheckedProgram} {budget fuel next : Nat}
    {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    ∀ index caller, next ≤ index → after.specializations[index]? = some caller →
      SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok () := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · cases accepted
  | succ fuel ih =>
    have growth := (SourcePreparedOpenCallEdges.aux accepted).1
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i ended
      cases accepted
      intro index caller bound found
      have length := List.getElem?_eq_none_iff.mp ended
      have present := (List.getElem?_eq_some_iff.mp found).1
      omega
    · rename_i caller found
      obtain ⟨checked, metadata, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨extended, _scan, remaining⟩ := bind_ok accepted
      intro index actual bound selected
      by_cases current : index = next
      · subst index
        have same := Option.some.inj (selected.symm.trans (growth.at found))
        subst actual
        exact metadata
      · exact ih remaining index actual (by omega) selected

/-- Metadata checks cover the complete prepared frontier. Original selected
rows are retained by the actual preparation and therefore have the same check. -/
theorem compiled_metadata (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations) :
    SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok () := by
  obtain ⟨prepared, accepted, growth, _⟩ :=
    SourcePreparedOpenCallEdges.of_validation compiled.plan_validated
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence
    SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp (growth.rows.entries.subset member)
  exact metadata_aux inspected index caller (Nat.zero_le _) found

private theorem forIn_nodes {ε : Type} {items : List Node}
    {checkExpression : ExpressionNode → Except ε Unit}
    {checkStatement : StatementNode → Except ε Unit}
    (accepted : (forIn items () fun (item : Node) _ =>
      match item with
      | .expression expression => do checkExpression expression; pure (ForInStep.yield ())
      | .statement statement => do checkStatement statement; pure (ForInStep.yield ())) = Except.ok ()) :
    ∀ expression, Node.expression expression ∈ items → checkExpression expression = .ok () := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, accepted⟩ := bind_ok accepted
    cases head with
    | expression head =>
      obtain ⟨checked, checkedEq, returned⟩ := bind_ok executed
      cases checked
      cases returned
      intro item member
      rcases List.mem_cons.mp member with current | later
      · cases current; exact checkedEq
      · exact ih accepted item later
    | statement head =>
      obtain ⟨checked, _checkedEq, returned⟩ := bind_ok executed
      cases checked
      cases returned
      intro item member
      rcases List.mem_cons.mp member with current | later
      · cases current
      · exact ih accepted item later

/-- A qualified original local reference uses its own ordinary requirement
spine. Coercion suffixes remain outside the exact template/actual pairing. -/
theorem metadata_bindings {caller : Specialized}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ())
    {node : ExpressionNode} (member : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) :
    ∃ owned substitution bindings,
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned ∧
      BindingsReceipt caller binder
        {node with type := node.rawType, requirements := owned, coercions := []} substitution bindings := by
  unfold SourceCompilationPlan.validateSpecializationMetadataWith at accepted
  simp only [Bool.true_or, bind,
    Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨staged, _staging, accepted⟩ := bind_ok accepted
  cases staged
  obtain ⟨checked, metadata, _remaining⟩ := bind_ok accepted
  cases checked
  run_tac unfoldCheck `metadata
  dsimp only at metadata
  obtain ⟨completed, scanned, _returned⟩ := bind_ok metadata
  cases completed
  have checkedNodes := forIn_nodes scanned
  have nodeChecked := checkedNodes node member
  try dsimp only at nodeChecked
  run_tac unfoldCheck `nodeChecked
  simp only [form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at nodeChecked
  split at nodeChecked <;> try contradiction
  cases ownedEq : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp only [ownedEq] at nodeChecked; cases nodeChecked
  | some owned =>
    have notEmpty : binder.schemeRequirements.isEmpty = false := List.isEmpty_eq_false_iff.mpr qualified
    simp only [ownedEq, found, notEmpty, Bool.false_eq_true, if_false] at nodeChecked
    run_tac unfoldCheck `nodeChecked
    obtain ⟨covered, _coverage, issued⟩ := bind_ok nodeChecked
    cases covered
    simp only [← form] at issued
    cases issuedEq : SourceCompilationPlan.localRequirementBindings caller binder
        {node with type := node.rawType, requirements := owned, coercions := []} with
    | error error =>
      simp only [issuedEq, Functor.discard, Functor.mapConst] at issued
      cases issued
    | ok result =>
      exact ⟨owned, result.1, result.2, rfl, bindings_receipt issuedEq⟩

/-- Public compiled objects authenticate these checks for every selected
original qualified local reference, without a source-typing premise. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} (present : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) :
    ∃ owned substitution bindings,
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned ∧
      BindingsReceipt caller binder
        {node with type := node.rawType, requirements := owned, coercions := []} substitution bindings :=
  metadata_bindings (compiled_metadata compiled member) present form found qualified

/-- The existing ground-predicate check can only remove variables owned by the
same inner scheme. Any captured variable would survive its exact matcher. -/
theorem BindingsReceipt.template_scoped
    {caller : Specialized} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (receipt : BindingsReceipt caller binder node substitution bindings)
    {template : LocalSchemeRequirement} (member : template ∈ binder.schemeRequirements)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables template.predicate) :
    metavariable ∈ binder.scheme.quantified := by
  have templates : bindings.map (fun binding => binding.template) = binder.schemeRequirements := by
    have paired := congrArg (List.map Prod.fst) receipt.pairs
    simpa only [List.map_map, Function.comp_def,
      List.map_fst_zip (Nat.le_of_eq receipt.count)] using paired
  obtain ⟨binding, present, equal⟩ := List.mem_map.mp (templates.symm ▸ member)
  subst template
  have checked := receipt.checked binding present
  have domain := (SourceSpecialization.matchClosedSchemeInstance?_sound receipt.matched).2.2.1
  by_cases quantified : metavariable ∈ binder.scheme.quantified
  · exact quantified
  apply False.elim
  have survives :=
    FlexibleSubstitution.Substitution.mem_predicateVariables_applySubstitution_of_not_mem_domain
      substitution (by rwa [domain]) occurs
  change metavariable ∈ TypedTraitResolution.predicateVariables
    (binding.template.applySubstitution substitution).predicate at survives
  rw [← checked.predicate, checked.ground] at survives
  exact List.not_mem_nil survives

/-- Every checked selected reference excludes variables outside that exact
inner scheme from its original template predicates. This leaves the lexical
owner and any outer/inner quantifier relationship visible to its consumer. -/
theorem compiled_template_excludes (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} (present : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ [])
    {template : LocalSchemeRequirement} (owned : template ∈ binder.schemeRequirements)
    {metavariable : TypeVarId} (outside : metavariable ∉ binder.scheme.quantified) :
    metavariable ∉ TypedTraitResolution.predicateVariables template.predicate := by
  obtain ⟨_owned, _substitution, _bindings, _spine, receipt⟩ :=
    compiled_selected compiled member present form found qualified
  exact fun occurs => outside (receipt.template_scoped owned occurs)

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
