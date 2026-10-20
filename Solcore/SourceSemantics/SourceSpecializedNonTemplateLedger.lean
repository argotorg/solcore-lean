import Lean
import Solcore.SourceSemantics.SourceCompiledSelectedFinalization
import Solcore.SourceSemantics.SubstitutionProperties

/-! The actual specialization guard closes every solved predicate outside
the source's owned template inventory, before any semantic body premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private instance : LawfulBEq RequirementId where
  eq_of_beq := by
    intro left right same
    cases left
    cases right
    simp_all [BEq.beq, instBEqRequirementId.beq]
  rfl := by intro value; cases value; simp [BEq.beq, instBEqRequirementId.beq]

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

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private def qualified (source : TypedSource) : List TypedBinder :=
  source.nodes.filterMap fun
    | .statement {form := .letDecl binder initializer, ..} =>
        if !binder.scheme.quantified.isEmpty &&
            initializer.any (SourceSpecialization.isDirectLambdaInitializer source)
        then some binder else none
    | _ => none

private def qualifiedIds (source : TypedSource) : List RequirementId :=
  ((qualified source).flatMap fun binder =>
    binder.schemeRequirements.map fun requirement => (binder, requirement)).map
      fun entry => entry.2.templateRequirement

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
                cases direct : SourceSpecialization.isDirectLambdaInitializer source initializer <;>
                  simp [empty, direct]

private theorem qualifiedIds_subset (source : TypedSource) :
    qualifiedIds source ⊆ sourceLocalSchemeTemplateIds source := by
  intro id member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  obtain ⟨binder, binderMember, pairMember⟩ := List.mem_flatMap.mp entryMember
  obtain ⟨requirement, schemeMember, pairEq⟩ := List.mem_map.mp pairMember
  subst entry
  rw [qualified_eq] at binderMember
  obtain ⟨binding, bindingMember, binderEq⟩ := List.mem_map.mp binderMember
  subst binder
  obtain ⟨statement, statementMember, form⟩ := localLambdaBindings_statement_origin bindingMember
  let owner : LocalSchemeTemplateOwner := {
    binder := binding.binder
    initializer := .expression binding.initializer
    requirement }
  apply sourceLocalSchemeTemplateIds_mem_iff.mpr
  refine ⟨owner, ?_, same⟩
  apply List.mem_flatMap.mpr
  refine ⟨{binder := binding.binder, initializer := .expression binding.initializer}, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨.statement statement, statementMember, ?_⟩
    change _ ∈ statementInitializedLetBindings statement.form
    rw [form]
    exact List.mem_singleton_self _
  · exact List.mem_map.mpr ⟨requirement, schemeMember, rfl⟩

private theorem concrete_closed {type : Ty}
    (concrete : SourceSpecialization.firstNonConcrete type = none) :
    type.freeVariables = [] := by
  induction type with
  | «variable» => cases concrete
  | parameter | constructor | error => rfl
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
      simp only [SourceSpecialization.firstNonConcrete] at concrete
      cases found : SourceSpecialization.firstNonConcrete left with
      | some reason => simp [found] at concrete
      | none =>
          have rightConcrete : SourceSpecialization.firstNonConcrete right = none := by
            simpa [found] using concrete
          have leftClosed := leftIH found
          have rightClosed := rightIH rightConcrete
          simp only [List.eq_nil_iff_forall_not_mem] at leftClosed rightClosed ⊢
          intro metavariable
          simp [leftClosed metavariable, rightClosed metavariable]
  | proxy inner ih | comptime inner ih => exact ih concrete

/-- The private executable guard supplies concrete types for this exact
solved row. Its exemption list consists only of genuine source templates. -/
theorem specialized_closed {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    {requirement : SolvedRequirement} (member : requirement ∈ row.function.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  unfold SourceSpecialization.specializeFunction at accepted
  iterate 5 have accepted := reject_ok accepted
  iterate 4 obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨ids, owned, accepted⟩ := bind_ok accepted
  obtain ⟨_, concrete, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical original) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
      subst row
      run_tac unfoldCheck `owned
      obtain ⟨_, _, owned⟩ := bind_ok owned
      dsimp only at owned
      split at owned <;> try cases owned
      iterate 2 obtain ⟨_, _, owned⟩ := bind_ok owned
      have idsEq : qualifiedIds (SourceSpecialization.applyCheckedFunction canonical original).typedBody = ids := by
        change Except.ok _ = Except.ok ids at owned
        exact Except.ok.inj owned
      have absent : requirement.id ∉ ids := by
        rw [← idsEq]
        exact fun contains => ordinary (qualifiedIds_subset _ contains)
      have filtered : requirement ∈
          ((SourceSpecialization.applyCheckedFunction canonical original).solvedRequirements.filter
            fun solved => !ids.contains solved.id) := by
        apply List.mem_filter.mpr
        exact ⟨member, by simp [absent]⟩
      run_tac unfoldCheck `concrete
      split at concrete
      · cases concrete
      · rename_i allConcrete
        have typeClosed (type : Ty)
            (present : type ∈ requirement.predicate.subject :: requirement.predicate.arguments) :
            type.freeVariables = [] := by
          apply concrete_closed
          apply (List.findSome?_eq_none_iff.mp allConcrete) type
          apply List.mem_append_right
          apply List.mem_flatMap.mpr
          refine ⟨requirement, filtered, ?_⟩
          exact List.mem_append_left _ present
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro metavariable occurs
        rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with
          subject | ⟨argument, argumentMember, argumentOccurs⟩
        · rw [typeClosed _ (List.mem_cons_self)] at subject
          cases subject
        · rw [typeClosed _ (List.mem_cons_of_mem _ argumentMember)] at argumentOccurs
          cases argumentOccurs

private theorem parameters_keep (parameters : ParameterSubstitution) (type : Ty) :
    type.freeVariables ⊆ (parameters.apply type).freeVariables := by
  intro metavariable occurs
  induction type with
  | «variable» value => exact occurs
  | parameter value | constructor value | error => cases occurs
  | proxy inner ih | comptime inner ih => exact ih occurs
  | application left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_application_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | function left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_function_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | product left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_product_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | mapping left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_mapping_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))

private theorem predicate_parameters_keep (parameters : ParameterSubstitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.predicateVariables predicate ⊆
      TypedTraitResolution.predicateVariables (ProgramPredicate.applyParameters parameters predicate) := by
  intro metavariable occurs
  apply TypedTraitResolution.mem_predicateVariables_iff.mpr
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, present, occurs⟩
  · exact .inl (parameters_keep parameters _ subject)
  · exact .inr ⟨parameters.apply argument, List.mem_map.mpr ⟨argument, present, rfl⟩,
      parameters_keep parameters argument occurs⟩

/-- Rigid specialization cannot hide a flexible variable from an original
predicate. The exact source inventory retains every template identifier. -/
theorem original_closed_of_application
    {row : SourceSpecialization.SpecializedFunction} {original : CheckedFunction}
    (closed : ∀ requirement ∈ row.function.solvedRequirements,
      requirement.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody →
      TypedTraitResolution.predicateVariables requirement.predicate = [])
    (same : row.function = SourceSpecialization.applyCheckedFunction row.parameterSubstitution original)
    {requirement : SolvedRequirement} (member : requirement ∈ original.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds original.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] := by
  let applied := SourceSpecialization.applySolvedRequirement row.parameterSubstitution requirement
  have appliedMember : applied ∈ row.function.solvedRequirements := by
    rw [same]
    exact List.mem_map.mpr ⟨requirement, member, rfl⟩
  have appliedOrdinary : applied.id ∉ sourceLocalSchemeTemplateIds row.function.typedBody := by
    rw [same]
    change requirement.id ∉ sourceLocalSchemeTemplateIds
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution original.typedBody)
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using ordinary
  have specializedClosed := closed applied appliedMember appliedOrdinary
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro metavariable occurs
  have kept := predicate_parameters_keep row.parameterSubstitution requirement.predicate occurs
  change metavariable ∈ TypedTraitResolution.predicateVariables applied.predicate at kept
  rw [specializedClosed] at kept
  cases kept

/-- The accepted specializer closes the original predicate too, before any
body typing or final generalization barrier is supplied. -/
theorem original_closed {signature : ProgramFunctionSignature}
    {original : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature original supplied = .ok row)
    {requirement : SolvedRequirement} (member : requirement ∈ original.solvedRequirements)
    (ordinary : requirement.id ∉ sourceLocalSchemeTemplateIds original.typedBody) :
    TypedTraitResolution.predicateVariables requirement.predicate = [] :=
  original_closed_of_application (fun _ member ordinary => specialized_closed accepted member ordinary)
    (SourceCompiledLocalReadOrigins.specializeFunction_applied accepted) member ordinary

end Solcore.SourceSemantics.SourceSpecializedNonTemplateLedger
