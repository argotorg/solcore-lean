import Lean
import Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner

/-! Successful selected specialization retains every source template in the
actual direct-lambda binding inventory used by prepared call discovery. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceSelectedTemplateInventory
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)
open SourceCompiledLocalFinalization

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

private def formBinders : StatementForm → List TypedBinder
  | .letDecl binder _ => [binder]
  | .forLoop initializer _ post _ => (initializer ++ post).filterMap fun
      | .letDecl binder _ => some binder
      | _ => none
  | .matchWith resolution => resolution.cases.flatMap fun arm =>
      match arm.pattern.resolution with
      | .binder binder => [binder]
      | .constructor _ instructions | .tuple instructions => instructions.filterMap fun
          | .binder binder => some binder
          | _ => none
      | _ => []
  | _ => []

private def expressionBinders : ExpressionForm → List TypedBinder
  | .lambda parameters _ _ => parameters
  | _ => []

private def nodeBinders : Node → List TypedBinder
  | .expression node => expressionBinders node.form
  | .statement statement => formBinders statement.form

private def allBinders (source : TypedSource) : List TypedBinder :=
  source.inputs ++ source.nodes.flatMap nodeBinders

private def qualified (source : TypedSource) : List TypedBinder :=
  source.nodes.filterMap fun
    | .statement {form := .letDecl binder initializer, ..} =>
        if !binder.scheme.quantified.isEmpty && initializer.any (SourceSpecialization.isDirectLambdaInitializer source)
        then some binder else none
    | _ => none

private theorem qualified_eq (source : TypedSource) :
    qualified source = (localLambdaBindings source).map (·.binder) := by
  change source.nodes.filterMap _ = (source.nodes.filterMap _).map _
  rw [List.map_filterMap]
  congr 1
  funext node
  cases node with
  | expression expression => rfl
  | statement statement =>
      cases statement with
      | mk id span type form =>
          cases form <;> try rfl
          rename_i binder initializer
          cases initializer with
          | none => simp
          | some initializer =>
              cases empty : binder.scheme.quantified.isEmpty <;>
                cases direct : SourceSpecialization.isDirectLambdaInitializer source initializer <;> simp [empty, direct]

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

/-- The actual private position check is unfolded; the returned witness comes
from its successful failed search, with the original complete binder retained. -/
private theorem specialized_qualified_id {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution} {row : Specialized}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    {binder : TypedBinder} (present : binder ∈ allBinders row.function.typedBody)
    (nonempty : binder.schemeRequirements ≠ []) :
    ∃ binding ∈ localLambdaBindings row.function.typedBody, binding.binder.id = binder.id := by
  unfold SourceSpecialization.specializeFunction at accepted
  iterate 5 have accepted := reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, residual, accepted⟩ := bind_ok accepted
  iterate 3 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical original) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst row
      run_tac unfoldCheck `residual
      obtain ⟨_, _, residual⟩ := bind_ok residual
      obtain ⟨_, positions, _⟩ := bind_ok residual
      run_tac unfoldCheck `positions
      change (match (allBinders (SourceSpecialization.applyCheckedFunction canonical original).typedBody).find?
        (fun candidate => !candidate.schemeRequirements.isEmpty &&
          !((qualified (SourceSpecialization.applyCheckedFunction canonical original).typedBody).map (·.id)).contains candidate.id) with
        | some candidate => Except.error (SourceSpecialization.Error.qualifiedBinderPosition candidate.id)
        | none => Except.ok ()) = (Except.ok _ : Except SourceSpecialization.Error Unit) at positions
      split at positions
      · cases positions
      · rename_i missing
        have checked := List.find?_eq_none.mp missing binder present
        have emptyFalse : binder.schemeRequirements.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
        simp only [emptyFalse, Bool.not_false, Bool.true_and, Bool.not_eq_true] at checked
        have known : binder.id ∈ (qualified (SourceSpecialization.applyCheckedFunction canonical original).typedBody).map (·.id) := by
          exact List.contains_iff_mem.mp ((show ∀ value : Bool, (!value) = false → value = true by decide) _ checked)
        rw [qualified_eq, List.map_map] at known
        obtain ⟨binding, member, same⟩ := List.mem_map.mp known
        exact ⟨binding, member, same⟩

private theorem flatMap_sublist {α β : Type} (values : List α) (f g : α → List β)
    (each : ∀ value, List.Sublist (f value) (g value)) : List.Sublist (values.flatMap f) (values.flatMap g) := by
  induction values with
  | nil => exact .refl _
  | cons head rest ih => exact (each head).append ih

private theorem forItem_ids (item : ForItemForm) :
    List.Sublist ((forItemInitializedLetBindings item).map fun binding => binding.binder.id)
      (forItemDefinedLocalIds item) := by
  cases item <;> try exact .refl _
  rename_i binder initializer
  cases initializer <;> simp [forItemInitializedLetBindings, forItemDefinedLocalIds]

private theorem form_ids (form : StatementForm) :
    List.Sublist ((statementInitializedLetBindings form).map fun binding => binding.binder.id)
      (statementDefinedLocalIds form) := by
  cases form <;> try exact List.nil_sublist _
  case letDecl binder initializer =>
    cases initializer <;> simp [statementInitializedLetBindings, statementDefinedLocalIds]
  case forLoop initial condition post body =>
    simp only [statementInitializedLetBindings, statementDefinedLocalIds, List.map_append, List.map_flatMap]
    exact (flatMap_sublist initial _ _ forItem_ids).append (flatMap_sublist post _ _ forItem_ids)

private theorem initialized_ids (source : TypedSource) :
    List.Sublist ((initializedLetBindings source).map fun binding => binding.binder.id)
      (definedLocalIds source) := by
  unfold initializedLetBindings definedLocalIds
  rw [List.map_flatMap]
  apply List.sublist_append_of_sublist_right
  apply flatMap_sublist
  intro node
  cases node with
  | expression expression => exact List.nil_sublist _
  | statement statement => exact form_ids statement.form

private theorem initialized_form_member {form : StatementForm} {binding : InitializedLetBinding}
    (member : binding ∈ statementInitializedLetBindings form) : binding.binder ∈ formBinders form := by
  cases form <;> simp only [statementInitializedLetBindings] at member <;> try cases member
  case letDecl binder initializer =>
    cases initializer with
    | none => cases member
    | some initializer =>
        have same := List.mem_singleton.mp member
        subst binding
        exact List.mem_singleton_self _
  case forLoop initial condition post body =>
    have joined : binding ∈ (initial ++ post).flatMap forItemInitializedLetBindings := by
      simpa only [List.flatMap_append] using member
    obtain ⟨item, itemMember, bound⟩ := List.mem_flatMap.mp joined
    cases item <;> simp only [forItemInitializedLetBindings] at bound <;> try cases bound
    rename_i binder initializer
    cases initializer with
    | none => cases bound
    | some initializer =>
        have same := List.mem_singleton.mp bound
        subst binding
        exact List.mem_filterMap.mpr ⟨.letDecl binder (some initializer), itemMember, rfl⟩

private theorem initialized_member {source : TypedSource} {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings source) : binding.binder ∈ allBinders source := by
  obtain ⟨node, nodeMember, bound⟩ := List.mem_flatMap.mp member
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨node, nodeMember, ?_⟩
  cases node with
  | expression expression => cases bound
  | statement statement => exact initialized_form_member bound

private theorem collector_initialized {source : TypedSource} {binding : LocalLambdaBinding}
    (member : binding ∈ localLambdaBindings source) :
    ({binder := binding.binder, initializer := .expression binding.initializer} : InitializedLetBinding) ∈ initializedLetBindings source := by
  obtain ⟨statement, present, form⟩ := localLambdaBindings_statement_origin member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, present, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

private theorem same_binding {values : List InitializedLetBinding}
    (unique : (values.map fun binding => binding.binder.id).Nodup)
    {left right : InitializedLetBinding} (lm : left ∈ values) (rm : right ∈ values)
    (same : left.binder.id = right.binder.id) : left = right := by
  induction values with
  | nil => cases lm
  | cons head rest ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp lm with leftHead | leftTail
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact leftHead.trans rightHead.symm
      · exact False.elim (absent (List.mem_map.mpr
          ⟨right, rightTail, same.symm.trans (congrArg (fun binding => binding.binder.id) leftHead)⟩))
    · rcases List.mem_cons.mp rm with rightHead | rightTail
      · exact False.elim (absent (List.mem_map.mpr
          ⟨left, leftTail, same.trans (congrArg (fun binding => binding.binder.id) rightHead)⟩))
      · exact ih unique leftTail rightTail


/-- The actual position guard and actual local identity uniqueness keep each
complete initialized template owner in the same discovery collector. -/
theorem specialized_binding {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution} {row : Specialized}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    (unique : LocalIdentityOwnership row.function.typedBody)
    {binding : InitializedLetBinding} (present : binding ∈ initializedLetBindings row.function.typedBody)
    (nonempty : binding.binder.schemeRequirements ≠ []) :
    ∃ owned ∈ localLambdaBindings row.function.typedBody, owned.binder = binding.binder := by
  obtain ⟨owned, member, same⟩ := specialized_qualified_id accepted (initialized_member present) nonempty
  have original := collector_initialized member
  have same := same_binding ((initialized_ids _).nodup unique.unique) original present same
  exact ⟨owned, member, congrArg InitializedLetBinding.binder same⟩

/-- The finalizer and specialization retain actual local/template identity
uniqueness for the selected source, without a whole-program typing premise. -/
theorem selected_ownership {compiled : SourceCoreCompiler.Compiled} {row : Specialized} {fuel : Nat}
    (selected : Selected compiled row fuel) :
    LocalIdentityOwnership row.function.typedBody ∧ LocalSchemeTemplateOwnership row.function.typedBody := by
  rw [selected.source]
  exact ⟨StructuralSubstitution.LocalIdentityOwnership.applyParameters _
      selected.body.resources.local_identity_ownership,
    StructuralSubstitution.LocalSchemeTemplateOwnership.applyParameters _
      selected.body.resources.ledger.templateOwnership⟩

/-- Raw compilation exposes both the actual position check and the identity
proof for each complete initialized binder in its selected rows. -/
theorem compile_binding {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations)
    {binding : InitializedLetBinding} (present : binding ∈ initializedLetBindings row.function.typedBody)
    (nonempty : binding.binder.schemeRequirements ≠ []) :
    ∃ owned ∈ localLambdaBindings row.function.typedBody, owned.binder = binding.binder := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  obtain ⟨original, _originalMember, signature, supplied, specialized⟩ := run_original ran member
  exact specialized_binding specialized (selected_ownership selected).1 present nonempty

/-- Every original finalized template occurs in the complete actual local
binding inventory consumed by prepared discovery. -/
theorem compile_inventory {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations)
    {id : RequirementId} (template : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    id ∈ (localLambdaBindings row.function.typedBody).flatMap fun binding =>
      binding.binder.schemeRequirements.map (·.templateRequirement) := by
  obtain ⟨owner, contains, same⟩ := sourceLocalSchemeTemplateIds_mem_iff.mp template
  have requirement := LocalSchemeTemplateOwner.requirement_mem contains
  have nonempty : owner.binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at requirement
    cases requirement
  obtain ⟨binding, present, binder⟩ := compile_binding accepted member
    (LocalSchemeTemplateOwner.binding_mem contains) nonempty
  apply List.mem_flatMap.mpr
  refine ⟨binding, present, ?_⟩
  rw [binder]
  exact List.mem_map.mpr ⟨owner.requirement, requirement, same⟩

/-- Actual contextual body validation assigns each original source template
used by this call to this same discovered instance. -/
theorem contextual_template {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (receipt : SourceCompiledTemplateCallOwner.PreparedContextual compiled caller node instantiation)
    {id : RequirementId} (template : id ∈ sourceLocalSchemeTemplateIds caller.function.typedBody)
    (issued : id ∈ node.requirements) :
    id ∈ receipt.contextual.localInstance.binding.binder.schemeRequirements.map (·.templateRequirement) := by
  have used : node ∈ localDeclarationUses receipt.bodyNodes := by
    apply List.mem_filterMap.mpr
    refine ⟨.expression node, receipt.nodeInBody, ?_⟩
    change (match (match node.form with
      | .call _ _ (.declaration value) | .reference _ (.declaration value) => some value
      | _ => none) with | some _ => some node | none => none) = some node
    rw [form]
  exact receipt.templates.foreign_mem used issued (compile_inventory accepted member template)

/-- The actual finalizer's template uniqueness identifies the complete
original template owner with the discovered instance's binder. -/
theorem contextual_owner {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (receipt : SourceCompiledTemplateCallOwner.PreparedContextual compiled caller node instantiation)
    {owner : LocalSchemeTemplateOwner} (contains : ContainsLocalSchemeTemplate caller.function.typedBody owner)
    (issued : owner.requirement.templateRequirement ∈ node.requirements) :
    owner.binder = receipt.contextual.localInstance.binding.binder ∧
      owner.requirement ∈ receipt.contextual.localInstance.binding.binder.schemeRequirements := by
  have template := sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
  obtain ⟨requirement, requirementMember, same⟩ := List.mem_map.mp
    (contextual_template accepted member form receipt template issued)
  have bindingMember := localLambdaInstances_bindings receipt.contextual.discovered
    receipt.contextual.localInstance receipt.contextual.member
  have initialized := collector_initialized bindingMember
  let owned : LocalSchemeTemplateOwner := {
    binder := receipt.contextual.localInstance.binding.binder
    initializer := .expression receipt.contextual.localInstance.binding.initializer
    requirement }
  have ownedContains : ContainsLocalSchemeTemplate caller.function.typedBody owned := by
    apply List.mem_flatMap.mpr
    refine ⟨_, initialized, ?_⟩
    exact List.mem_map.mpr ⟨requirement, requirementMember, rfl⟩
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  have ownerEq := (selected_ownership selected).2.owner_unique contains ownedContains same.symm
  exact ⟨congrArg (fun owner : LocalSchemeTemplateOwner => owner.binder) ownerEq,
    (congrArg (fun owner : LocalSchemeTemplateOwner => owner.requirement) ownerEq).symm ▸ requirementMember⟩

/-- Every variable in this original template is scoped by the same actual
inner binder, derived from the public compiler's qualified-read metadata. -/
theorem contextual_predicate_scoped {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (receipt : SourceCompiledTemplateCallOwner.PreparedContextual compiled caller node instantiation)
    {owner : LocalSchemeTemplateOwner} (contains : ContainsLocalSchemeTemplate caller.function.typedBody owner)
    (issued : owner.requirement.templateRequirement ∈ node.requirements)
    {metavariable : TypeVarId} (occurs : metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate) :
    metavariable ∈ owner.binder.scheme.quantified := by
  obtain ⟨same, requirement⟩ := contextual_owner accepted member form receipt contains issued
  rw [same]
  exact SourcePreparedQualifiedLocalReadOwner.compiled_instance_template_scoped compiled member
    receipt.contextual.discovered receipt.contextual.member requirement occurs

/-- An original template's actual emitter is either closed, or its predicate
is scoped entirely by its same complete discovered lexical owner. The closed
branch retains the exact emitter for the subsequent raw-predicate join. -/
theorem compile_owner_outcome {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {owner : LocalSchemeTemplateOwner} (contains : ContainsLocalSchemeTemplate caller.function.typedBody owner) :
    ∃ node, .expression node ∈ caller.function.typedBody.nodes ∧
      ∃ callee arguments instantiation,
        node.form = .call callee arguments (.declaration instantiation) ∧
        owner.requirement.templateRequirement ∈ node.requirements ∧
        instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id) ∧
        (SourcePreparedOpenCallEdges.InstantiationClosed instantiation = true ∨
          (∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
            metavariable ∈ owner.binder.scheme.quantified)) := by
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, alternative⟩ :=
    SourceCompiledTemplateCallOwner.template_owner accepted member
      (sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩)
  refine ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, ?_⟩
  rcases alternative with closed | contextual
  · exact .inl closed
  · obtain ⟨receipt⟩ := contextual
    exact .inr (fun _ occurs => contextual_predicate_scoped accepted member form receipt contains issued occurs)

end Solcore.SourceSemantics.SourceSelectedTemplateInventory
