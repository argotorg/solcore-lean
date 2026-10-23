import Lean
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality

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
