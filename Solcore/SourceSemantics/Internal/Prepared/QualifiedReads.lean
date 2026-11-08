import Lean
import Solcore.SourceSemantics.Internal.Prepared.PlanGrowth
import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.Internal.Compiled.Origins

/-!
# Qualified local reads

Qualified local reads in a prepared row keep their matching binding, owner and resolved witness
factory, and template coverage excludes them from template uses.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedLocalReadTemplateExclusion
/-! Actual template coverage excludes every local reference from template uses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.SourcePreparedLocalReadTemplateExclusion
open Frontend SourceInference TypeSystem
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

open Lean Meta Elab Term in
private def actualDefinition (original : Name) : TermElabM Lean.Expr := do
  let mut found : Option Name := none
  for (name, _) in (← getEnv).constants.toList do
    if privateToUserName? name == some original then
      if found.isSome then throwError "ambiguous actual coverage definition: {original}"
      found := some name
  let some name := found | throwError "missing actual coverage definition: {original}"
  mkConstWithFreshMVarLevels name
elab "actual_template_coverage" : term => actualDefinition `Solcore.Frontend.SourceCompilationPlan.validateQualifiedLocalTemplateCoverage

open Lean Meta Elab Tactic in
private def unfoldCheck (hypothesis : Name) : TacticM Unit := withMainContext do
  let declaration ← getLocalDeclFromUserName hypothesis
  let type ← instantiateMVars (← inferType declaration.toExpr)
  let some (_, left, _) := type.eq? | throwError "expected equation: {type}"
  let .const name _ := left.getAppFn | throwError "expected actual definition: {left}"
  let goal ← getMainGoal
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

private theorem forIn_checked {α ε : Type} {items : List α}
    {step : α → Unit → Except ε (ForInStep Unit)} {property : α → Prop}
    (accepted : forIn items () step = .ok ())
    (each : ∀ item outcome, step item () = .ok outcome →
      outcome = .yield () ∧ property item) :
    ∀ item ∈ items, property item := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, remaining⟩ := bind_ok accepted
    obtain ⟨rfl, proved⟩ := each first outcome executed
    intro item present
    rcases List.mem_cons.mp present with rfl | later
    · exact proved
    · exact ih remaining item later

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

private theorem coverage_of_metadata {caller : Specialized}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ())
    {node : ExpressionNode} (member : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) :
    ∃ owned, SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned ∧
      actual_template_coverage caller
        {node with type := node.rawType, requirements := owned, coercions := []} binder = .ok () := by
  unfold SourceCompilationPlan.validateSpecializationMetadataWith at accepted
  simp only [Bool.true_or, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  obtain ⟨staged, _staging, accepted⟩ := bind_ok accepted
  cases staged
  obtain ⟨checked, metadata, _remaining⟩ := bind_ok accepted
  cases checked
  run_tac unfoldCheck `metadata
  dsimp only at metadata
  obtain ⟨completed, scanned, _returned⟩ := bind_ok metadata
  cases completed
  have nodeChecked := forIn_nodes scanned node member
  try dsimp only at nodeChecked
  run_tac unfoldCheck `nodeChecked
  simp only [form, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at nodeChecked
  split at nodeChecked <;> try contradiction
  cases ownedEq : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp only [ownedEq] at nodeChecked; cases nodeChecked
  | some owned =>
    have notEmpty := List.isEmpty_eq_false_iff.mpr qualified
    simp only [ownedEq, found, notEmpty, Bool.false_eq_true, if_false] at nodeChecked
    run_tac unfoldCheck `nodeChecked
    obtain ⟨covered, coverage, _issued⟩ := bind_ok nodeChecked
    cases covered
    exact ⟨owned, rfl, coverage⟩

private theorem coverage_excludes_local {caller : Specialized}
    {node : ExpressionNode} {binder : TypedBinder}
    (coverage : actual_template_coverage caller node binder = .ok ())
    {template : LocalSchemeRequirement} (templateMember : template ∈ binder.schemeRequirements)
    {read : ExpressionNode} (readMember : .expression read ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : read.form = .reference name (.local localId)) :
    template.templateRequirement ∉ read.requirements := by
  run_tac unfoldCheck `coverage
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at coverage
  split at coverage <;> try contradiction
  split at coverage <;> try contradiction
  split at coverage <;> try contradiction
  obtain ⟨checked, _uses, coverage⟩ := bind_ok coverage
  cases checked
  obtain ⟨checked, templates, _returned⟩ := bind_ok coverage
  cases checked
  have each := forIn_checked templates (property := fun item : LocalSchemeRequirement =>
    item.templateRequirement ∉ read.requirements) (by
      intro item outcome iteration
      try dsimp only at iteration
      split at iteration <;> try contradiction
      rename_i declarationUse onlyUse
      have excludes : item.templateRequirement ∉ read.requirements := by
        intro used
        have present : read ∈ [declarationUse] := by
          rw [← onlyUse]
          apply List.mem_filterMap.mpr
          exact ⟨.expression read, readMember, by simp [used]⟩
        have same := List.mem_singleton.mp present
        subst declarationUse
        split at iteration <;> try contradiction
        split at iteration <;> try contradiction
        split at iteration <;> try contradiction
        simp only [form] at iteration
        contradiction
      refine ⟨?_, excludes⟩
      split at iteration <;> try contradiction
      split at iteration <;> try contradiction
      split at iteration <;> try contradiction
      split at iteration <;> try contradiction
      all_goals split at iteration <;> cases iteration <;> rfl)
  exact each template templateMember

/-- The actual global metadata check reserves each template occurrence for a
single declaration use. It cannot occur on any local reference, including its
coercion requirement suffix. -/
theorem metadata_template_excluded {caller : Specialized}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ())
    {node : ExpressionNode} (member : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    {template : LocalSchemeRequirement} (templateMember : template ∈ binder.schemeRequirements)
    {read : ExpressionNode} (readMember : .expression read ∈ caller.function.typedBody.nodes)
    {readName : String} {readId : Resolved.LocalId}
    (readForm : read.form = .reference readName (.local readId)) :
    template.templateRequirement ∉ read.requirements := by
  have qualified : binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at templateMember
    exact List.not_mem_nil templateMember
  obtain ⟨_owned, _layout, coverage⟩ := coverage_of_metadata accepted member form found qualified
  exact coverage_excludes_local coverage templateMember readMember readForm

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

/-- The actual witness loop only issues template identities from this binder. -/
theorem witness_template_member {caller : Specialized}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder}
    {node : ExpressionNode} {substitution : Substitution}
    {witnesses : List SourceTypedRuntime.LocalRequirementWitness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node =
      .ok (substitution, witnesses)) :
    ∀ witness ∈ witnesses, ∃ template ∈ binder.schemeRequirements,
      witness.templateRequirement = template.templateRequirement := by
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨matched, bindings⟩, bound, accepted⟩ := bind_ok accepted
  have paired := (SourcePreparedQualifiedLocalReadBindings.bindings_receipt bound).pairs
  obtain ⟨final, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant (invariant := fun current => ∀ witness ∈ current,
    ∃ template ∈ binder.schemeRequirements,
      witness.templateRequirement = template.templateRequirement) loop
  · simp
  · intro binding member current outcome prior iteration
    have both : (binding.template, binding.actualRequirement) ∈
        binder.schemeRequirements.zip node.requirements := by
      rw [← paired]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    have templateMember := (List.of_mem_zip both).1
    dsimp only at iteration
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at iteration
    split at iteration
    · cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness present
      rcases List.mem_append.mp present with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact ⟨binding.template, templateMember, rfl⟩
    · split at iteration <;> try contradiction
      cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness present
      rcases List.mem_append.mp present with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact ⟨binding.template, templateMember, rfl⟩

/-- A real factory for a validated binder never rewrites a local-reference
requirement in the same original caller. Substituting types does not change
these identities, so the result also applies at the actual rewrite step. -/
theorem factory_read_unchanged {caller : Specialized}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ())
    {node : ExpressionNode} (member : .expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId}
    (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (found : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    {factoryCaller : Specialized} {available : SourceCompilationPlan.EvidenceEnvironment}
    {active child : Substitution} {factoryNode : ExpressionNode}
    {witnesses : List SourceTypedRuntime.LocalRequirementWitness}
    (factory : SourceCompilationPlan.localRequirementWitnesses factoryCaller available
      (binder.applySubstitution active) factoryNode = .ok (child, witnesses))
    {read : ExpressionNode} (readMember : .expression read ∈ caller.function.typedBody.nodes)
    {readName : String} {readId : Resolved.LocalId}
    (readForm : read.form = .reference readName (.local readId))
    (substitution : Substitution) :
    SourceTypedRuntime.rewriteExpressionLocalRequirements witnesses
      (read.applySubstitution substitution) = read.applySubstitution substitution := by
  have absent : ∀ witness ∈ witnesses, witness.templateRequirement ∉ read.requirements := by
    intro witness present
    obtain ⟨template, templateMember, same⟩ := witness_template_member factory witness present
    change template ∈ binder.schemeRequirements.map _ at templateMember
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp templateMember
    change witness.templateRequirement = original.templateRequirement at same
    rw [same]
    exact metadata_template_excluded accepted member form found originalMember readMember readForm
  have spine : read.requirements.map (SourceTypedRuntime.rewriteLocalRequirement witnesses) =
      read.requirements := by
    apply (List.map_congr_left (g := id) ?_).trans (List.map_id _)
    intro requirement present
    unfold SourceTypedRuntime.rewriteLocalRequirement
    cases selected : witnesses.find? (fun witness => witness.templateRequirement == requirement) with
    | none => rfl
    | some witness =>
      have equal : witness.templateRequirement = requirement := by
        simpa using List.find?_some selected
      exact False.elim (absent witness (List.mem_of_find?_eq_some selected) (equal.symm ▸ present))
  cases read
  simp only [SourceTypedRuntime.rewriteExpressionLocalRequirements,
    ExpressionNode.applySubstitution, spine]

end Solcore.SourceSemantics.SourcePreparedLocalReadTemplateExclusion
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
/-! Actual local-instance discovery and original metadata validation select
the same complete lexical owner. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
open Frontend SourceInference SourceSpecializationWorklist TypeSystem

private theorem lookup_eq_head (source : TypedSource) (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? source id =
      ((localLambdaBindings source).filter (fun binding => binding.binder.id == id)).head?.map
        (fun binding => binding.binder) := by
  have collected : localLambdaBindings source = source.nodes.filterMap (fun
      | .statement {form := .letDecl binder (some initializer), ..} =>
          if binder.scheme.quantified.isEmpty ||
              !SourceSpecialization.isDirectLambdaInitializer source initializer then none
          else some ({binder, initializer} : LocalLambdaBinding)
      | _ => none) := rfl
  rw [collected, ← List.head?_map, List.filter_filterMap, List.map_filterMap, List.head?_filterMap]
  unfold SourceCompilationPlan.directLambdaLetBinder?
  congr 1
  funext node
  cases node with
  | expression expression => rfl
  | statement statement =>
    cases statement with
    | mk sid span type form =>
      cases form <;> try rfl
      rename_i binder initializer
      cases initializer with
      | none => rfl
      | some initializer =>
        by_cases same : binder.id = id <;>
          cases empty : binder.scheme.quantified.isEmpty <;>
          cases direct : SourceSpecialization.isDirectLambdaInitializer source initializer <;>
          simp [same, empty, direct, Option.filter]

/-- Exact worklist selection fixes the result of the metadata owner's
first-match lookup, including the complete binder and its templates. -/
theorem selected_owner {source : TypedSource} {binding : LocalLambdaBinding}
    (selected : LocalLambdaBinding.Selected (localLambdaBindings source) binding) :
    SourceCompilationPlan.directLambdaLetBinder? source binding.binder.id = some binding.binder := by
  rw [lookup_eq_head]
  change ((localLambdaBindings source).filter
    (fun candidate => candidate.binder.id == binding.binder.id)).head?.map _ = _
  rw [selected]
  rfl

/-- Discovery supplies the exact owner selection for every root and
contextual instance. No uniqueness premise is added at the public boundary. -/
theorem discovered_owner {source : TypedSource} {contextFuel : Option Nat}
    {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances source contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances) :
    SourceCompilationPlan.directLambdaLetBinder? source localInstance.binding.binder.id =
      some localInstance.binding.binder :=
  selected_owner (localLambdaInstances_selected discovered localInstance member)

/-- The same discovered instance yields an original local reference and its
actual qualified metadata receipt, even when discovery used a parent context. -/
theorem compiled_instance (compiled : SourceCoreCompiler.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations)
    {contextFuel : Option Nat} {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances caller.function.typedBody contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances)
    (qualified : localInstance.binding.binder.schemeRequirements ≠ []) :
    ∃ node name owned substitution bindings,
      Node.expression node ∈ caller.function.typedBody.nodes ∧
      node.form = .reference name (.local localInstance.binding.binder.id) ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned ∧
      SourcePreparedQualifiedLocalReadBindings.BindingsReceipt caller localInstance.binding.binder
        {node with type := node.rawType, requirements := owned, coercions := []} substitution bindings := by
  have owner := discovered_owner discovered member
  have origin := localLambdaInstances_read_origin discovered localInstance member
  cases origin with
  | root node present name form matched =>
      obtain ⟨owned, substitution, bindings, spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.compiled_selected compiled selected present form owner qualified
      exact ⟨node, name, owned, substitution, bindings, present, form, spine, receipt⟩
  | contextual parentOrigin node present name form child matched cumulative =>
      obtain ⟨owned, substitution, bindings, spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.compiled_selected compiled selected present form owner qualified
      exact ⟨node, name, owned, substitution, bindings, present, form, spine, receipt⟩

/-- Every original template of an actual discovered instance is scoped only
by that instance's complete inner binder. -/
theorem compiled_instance_template_scoped (compiled : SourceCoreCompiler.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations)
    {contextFuel : Option Nat} {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances caller.function.typedBody contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances)
    {template : LocalSchemeRequirement} (owned : template ∈ localInstance.binding.binder.schemeRequirements)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables template.predicate) :
    metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  have qualified : localInstance.binding.binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at owned
    exact List.not_mem_nil owned
  obtain ⟨_node, _name, _owned, _substitution, _bindings, _present, _form, _spine, receipt⟩ :=
    compiled_instance compiled selected discovered member qualified
  exact receipt.template_scoped owned occurs

/-- Successful checked compilation supplies the actual instance discovery
and the same-owner template scoping for every selected source row. -/
theorem compileChecked_instance_templates
    {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances caller.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∀ template ∈ localInstance.binding.binder.schemeRequirements,
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables template.predicate,
          metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  obtain ⟨instances, discovered, _origins⟩ :=
    SourceCompiledLocalReadOrigins.compileChecked_local_instances accepted selected
  exact ⟨instances, discovered, fun _ member _ owned _ occurs =>
    compiled_instance_template_scoped compiled selected discovered member owned occurs⟩

/-- The public raw-source compiler provides the same receipt without a
separate discovery, owner equality, or source typing assumption. -/
theorem compile_instance_templates
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances caller.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∀ template ∈ localInstance.binding.binder.schemeRequirements,
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables template.predicate,
          metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  obtain ⟨instances, discovered, _origins⟩ :=
    SourceCompiledLocalReadOrigins.compile_local_instances accepted selected
  exact ⟨instances, discovered, fun _ member _ owned _ occurs =>
    compiled_instance_template_scoped compiled selected discovered member owned occurs⟩

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
end

section
-- leanmerge: from Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
/-! The executable-plan preparation actually resolves and checks the witness
factory for every qualified local reference in each selected original row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
open Frontend SourceInference SourceSpecializationWorklist TypeSystem
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

open Lean Meta Elab Tactic in
private def unfoldCheck (hypothesis : Name) : TacticM Unit := withMainContext do
  let declaration ← getLocalDeclFromUserName hypothesis
  let type ← instantiateMVars (← inferType declaration.toExpr)
  let some (_, left, _) := type.eq? | throwError "expected equation: {type}"
  let .const name _ := left.getAppFn | throwError "expected actual definition: {left}"
  let goal ← getMainGoal
  replaceMainGoal [← unfoldLocalDecl goal declaration.fvarId name]

/-- The complete actual resolver and witness equations are retained together. -/
def Covered (program : CheckedProgram) (caller : Specialized) : Prop :=
  ∃ available,
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
    ∀ node, Node.expression node ∈ caller.function.typedBody.nodes →
      ∀ name localId, node.form = .reference name (.local localId) →
      ∀ binder, SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder →
      binder.schemeRequirements ≠ [] →
      ∃ substitution witnesses, SourceCompilationPlan.localRequirementWitnesses caller available binder node =
        .ok (substitution, witnesses)

private theorem forIn_each {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {property : α → Prop}
    (accepted : forIn items initial step = .ok final)
    (each : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ after, outcome = .yield after ∧ property item) :
    ∀ item ∈ items, property item := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, remaining⟩ := bind_ok accepted
    obtain ⟨after, rfl, checked⟩ := each item List.mem_cons_self initial outcome executed
    intro actual member
    rcases List.mem_cons.mp member with rfl | later
    · exact checked
    · exact ih remaining (fun next present => each next (List.mem_cons_of_mem item present)) actual later

/-- The actual frontier scan supplies these receipts even for helper rows
appended during evidence preparation. -/
theorem aux {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    ∀ index caller, next ≤ index → after.specializations[index]? = some caller → Covered program caller := by
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
      obtain ⟨checked, _metadata, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨extended, scan, remaining⟩ := bind_ok accepted
      intro index actual bound selected
      by_cases current : index = next
      · subst index
        have same := Option.some.inj (selected.symm.trans (growth.at found))
        subst actual
        obtain ⟨available, resolved, scan⟩ := bind_ok scan
        obtain ⟨final, loop, returned⟩ := bind_ok scan
        cases returned
        refine ⟨available, resolved, ?_⟩
        have result := forIn_each (property := fun item =>
          ∀ node, item = Node.expression node → ∀ name localId,
            node.form = .reference name (.local localId) → ∀ binder,
            SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder →
            binder.schemeRequirements ≠ [] → ∃ substitution witnesses,
              SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses))
          loop ?_
        · intro node member
          exact result _ member node rfl
        intro item _ previous outcome executed
        cases item with
        | statement statement =>
          cases executed
          exact ⟨previous, rfl, fun _ same => by cases same⟩
        | expression node =>
          have originalExecuted := executed
          have yielded : ∃ after, outcome = .yield after := by
            cases form : node.form <;> simp only [form] at executed
            case' call callee arguments resolution => cases resolution
            case' reference name resolution => cases resolution
            all_goals
              iterate 20 all_goals first
                | exact ⟨_, (Except.ok.inj executed).symm⟩
                | (obtain ⟨value, _action, executed⟩ := bind_ok executed)
                | split at executed
                | contradiction
          obtain ⟨after, rfl⟩ := yielded
          refine ⟨after, rfl, ?_⟩
          intro actual same name localId form binder detected qualified
          cases same
          simp only [form] at originalExecuted
          obtain ⟨coercionPlan, _coercions, checked⟩ := bind_ok originalExecuted
          have nonempty : binder.schemeRequirements.isEmpty = false := List.isEmpty_eq_false_iff.mpr qualified
          simp only [detected, nonempty, Bool.false_eq_true, if_false] at checked
          obtain ⟨validated, evidence, _returned⟩ := bind_ok checked
          cases validated
          run_tac unfoldCheck `evidence
          obtain ⟨witnesses, witnessesAccepted, _validated⟩ := bind_ok evidence
          run_tac unfoldCheck `witnessesAccepted
          obtain ⟨covered, _coverage, witnessesAccepted⟩ := bind_ok witnessesAccepted
          cases covered
          obtain ⟨pair, factory, _returned⟩ := bind_ok witnessesAccepted
          exact ⟨pair.1, pair.2, factory⟩
      · exact ih remaining index actual (by omega) selected

/-- Every complete row retained by a successful preparation has been scanned. -/
theorem prepared_selected {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations) : Covered program caller := by
  unfold SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact aux inspected index caller (Nat.zero_le _) found

/-- Compilation supplies the actual witness factory on each retained selected
row; neither a caller-supplied factory result nor evidence coverage is assumed. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations) :
    Covered compiled.program caller := by
  obtain ⟨prepared, accepted, growth, _⟩ := SourcePreparedOpenCallEdges.of_validation compiled.plan_validated
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence
    SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget at accepted
  obtain ⟨scanned, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨checked, _canonical, returned⟩ := bind_ok accepted
  cases checked
  cases returned
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp (growth.rows.entries.subset member)
  exact aux inspected index caller (Nat.zero_le _) found

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
end
