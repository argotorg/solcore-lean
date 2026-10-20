import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces

/-! The original selected checker call supplies the complete recursive body
entry. Only the declared input parameters are monomorphic; no condition is
placed on local schemes introduced by the body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem selected_original_interfaces (selected : Selected compiled row fuel)
    (member : row ∈ compiled.plan.specializations) :
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource := by
  have validated := compiled.plan_validated
  unfold SourceCompilationPlan.validateExecutablePlanEvidence at validated
  cases prepared : SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan with
  | error error => rw [prepared] at validated; cases validated
  | ok plan =>
      have covered := CoreLowering.CallableCoercionPreparation.of_accepted_with prepared
      have actual := CoreLowering.SelectedCompilationCoercionInterfaces.of_covered
        (covered.2 row (covered.1.entries.subset member))
      rw [selected.specialized] at actual
      have original := CoreLowering.SelectedCompilationCoercionInterfaces.of_applied actual
      simpa only [checkingContext, context, ExecutableCoercionInterfaces.BodyInterfaces, selected.body.source,
        selected.body.solved] using original

theorem selected_body_header {raw : Workspace.RawWorkspace}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    CheckedBodyHeaderWellFormed compiled.program.signatures selected.signature selected.original := by
  obtain ⟨signature, member, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram checked selected.originalMember
  have same := eq_of_mem_of_nodup_map
    (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids member selected.signatureMember
    (header.declaration_eq.symm.trans
      (checkFunctionBody_success_declaration selected.body.accepted))
  subst signature
  exact header

private theorem input_context_fields {owner : Resolved.DeclarationId}
    {base target : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types target) :
    target.signatures = base.signatures ∧
    target.typeParameters = base.typeParameters ∧
    target.currentDeclaration = base.currentDeclaration ∧
    target.residualTypeVariables = base.residualTypeVariables ∧
    target.solvedRequirements = base.solvedRequirements := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons _ head _ ih =>
      exact ⟨ih.1.trans head.context_fields.1,
        ih.2.1.trans head.context_fields.2.2.1,
        ih.2.2.1.trans head.context_fields.2.1,
        ih.2.2.2.1.trans head.residualTypeVariables_eq,
        ih.2.2.2.2.trans head.context_fields.2.2.2.2⟩

private theorem input_type_formed {owner : Resolved.DeclarationId}
    {base target : SourceSemantics.Context} {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner base binders types target) {type : Ty}
    (formed : TypeWellFormed base type) : TypeWellFormed target type := by
  induction extension with
  | nil => exact formed
  | cons _ head _ ih =>
      cases head
      exact ih (formed.withLocal _ _ _)

private theorem returned_source (selected : Selected compiled row fuel) :
    evidenceSource selected = selected.body.body.state.toTypedSource (bodyRoots selected) := by
  have header := Detail.unify_state_header selected.body.unified
  have owner := congrArg State.Header.owner header
  have inputs := congrArg State.Header.inputs header
  change selected.body.returned.owner = selected.body.body.state.owner at owner
  change selected.body.returned.inputs = selected.body.body.state.inputs at inputs
  simp only [evidenceSource, State.toTypedSource, owner, inputs, selected.body.returned_nodes]

structure BodyEntry (selected : Selected compiled row fuel)
    (target : SourceSemantics.Context) : Prop where
  inputs : MonoBindersExtend selected.signature.id
    (checkedBodyContext compiled.program.signatures selected.signature selected.original)
    selected.original.typedBody.inputs selected.signature.parameterTypes target
  returnSafe : ∀ binder ∈ (initial selected.signature selected.body.declaration).localBinders,
    ProtectedVariables.Safe binder.scheme.quantified
      (initial selected.signature selected.body.declaration)
      (Ty.productMany selected.signature.returnTypes)
  returnAdmissible : TypeAdmissible target
    (selected.body.finalized.substitution.apply (Ty.productMany selected.signature.returnTypes))
  boundary : StatementsBoundary selected fuel (checkingContext selected)
    selected.signature.source.value.body.value (Ty.productMany selected.signature.returnTypes)
    (initial selected.signature selected.body.declaration) selected.body.body [] target

/-- All entry conditions belong to the same original successful body check.
Actual executable preparation supplies the complete source interfaces. -/
theorem body_entry_of_interfaces {raw : Workspace.RawWorkspace}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource) :
    ∃ target, BodyEntry selected target := by
  have header := selected_body_header selected checked
  obtain ⟨target, inputs⟩ := header.inputs_extend
  have progress := selected.inferenceProgress checked
  have owner : selected.body.declaration.id = selected.signature.id :=
    (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have inputExtension : MonoBindersExtend selected.body.declaration.id
      (checkedBodyContext compiled.program.signatures selected.signature selected.original)
      ((initial selected.signature selected.body.declaration).localBinders.map
        (TypedBinder.applySubstitution selected.body.finalized.substitution))
      selected.signature.parameterTypes target := by
    have actualInputs := checkFunctionBody_success_typedBody_inputs selected.body.accepted
    rw [actualInputs, selected.body.substitution, ← owner] at inputs
    simpa only [initial, State.initial_inputs_eq_localBinders] using inputs
  have active : ActiveLocalContextInvariant (initial selected.signature selected.body.declaration)
      selected.body.finalized.substitution target := by
    constructor
    · exact LocalEnvironmentAligned.ofInitialMonoBindersExtend _ _ _ _
        (context := checkedBodyContext compiled.program.signatures selected.signature selected.original)
        (final := target) (types := selected.signature.parameterTypes) rfl rfl inputExtension
    · exact ActiveLocalFormation.ofMonoBindersExtend inputExtension
  have predicatesFixed : selected.signature.scheme.predicates.map
      (TypedTraitResolution.applySubstitution selected.body.finalized.substitution) =
        selected.signature.scheme.predicates :=
    ((Frontend.checkProgram_success_signature_formation checked).functions
      selected.signature selected.signatureMember).2.2.apply_eq_self _
  have emptyActual : ActualContext (checkingContext selected) selected.body.finalized []
      (checkedBodyContext compiled.program.signatures selected.signature selected.original) := by
    apply ActualContext.empty
    · rfl
    · simp only [checkingContext, context, checkedBodyContext, declarationContext,
        finalizedRequirementContext, Context.withResidualTypeVariables,
        Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration,
        predicatesFixed]
    · rw [← selected.body.source]
      simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, owner] using
        checkFunctionBody_success_typedBody_owner selected.body.accepted
  have actual := emptyActual.monoBinders inputs
  have fields := input_context_fields inputs
  have invariant : RecursiveStatementInvariant (checkingContext selected)
      (Ty.productMany selected.signature.returnTypes) selected.body.finalized
      (initial selected.signature selected.body.declaration) target := by
    refine {
      active
      ready := progress.initialReady
      returnBelow := progress.returnBelow
      bindersBelow := State.initial_localBindersBelowNextLocal _ _ _
      nodesBelow := State.initial_nodesBelowNextOccurrence _ _ _
      schemeIsolation := ?_
      substitutionExtension := progress.initial_substitution
      signaturesEq := fields.1
      typeParametersEq := fields.2.1
      declarationEq := ?_
      residual := fields.2.2.2.1
      solvedRequirementsEq := ?_
      assumptionsMono := ?_ }
    · apply activeSchemeQuantifierIsolation_initial_mono
      intro entry present
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp present
      rfl
    · simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, owner,
        checkedBodyContext, declarationContext, Context.withResidualTypeVariables,
        Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration] using fields.2.2.1
    · simpa only [checkedBodyContext, declarationContext, finalizedRequirementContext,
        Context.withResidualTypeVariables, Context.withSolvedRequirements,
        Context.withAssumptions, Context.forDeclaration, selected.body.solved] using fields.2.2.2.2
    · intro predicate present
      rw [actual.assumptions_eq]
      exact List.mem_append_left _ present
  have returnFixed : selected.body.finalized.substitution.apply
      (Ty.productMany selected.signature.returnTypes) = Ty.productMany selected.signature.returnTypes := by
    have resultType : selected.body.finalized.type = Ty.productMany selected.signature.returnTypes := by
      simpa only [selected.body.checkedResult] using header.result_type
    exact (Detail.finalize_type selected.body.finalization).symm.trans resultType
  refine ⟨target, inputs, ?_, ?_, ?_⟩
  · intro binder present
    exact ProtectedVariables.safe_closed _ _
      (Ty.variablesBelow_productMany
        (((Frontend.checkProgram_success_signature_formation checked).functions
          selected.signature selected.signatureMember).2.1.variablesBelow 0))
  · rw [returnFixed]
    exact TypeAdmissible.ofWellFormed (input_type_formed inputs
      ⟨header.parameter_binders, StructuralSubstitution.TypesWellScoped.productMany
        (StructuralSubstitution.TypesWellFormed.toTypesWellScoped header.return_types)⟩)
  · refine {
      accepted := selected.body.inferred
      interfaces := interfaces
      extension := progress.final_substitution
      scope := .refl selected
      invariant
      actual
      operational := ?_
      rawSubtrees := ?_
      integerPatterns := ?_
      integerLiterals := ?_
      requirements := ?_
      covered := ?_
      actualCovered := ?_ }
    · apply GeneralizedActualStateInvariant.initial
      intro entry present
      obtain ⟨parameter, _, rfl⟩ := List.mem_map.mp present
      rfl
    · intro child _
      rw [returned_source selected]
      exact RawSubtreePreserved.ofTypingSourceExtends (.refl _)
    · rw [Detail.unify_integerPatterns selected.body.unified]
      exact List.Subset.refl _
    · rw [Detail.unify_integerLiterals selected.body.unified]
      exact List.Subset.refl _
    · rw [selected.body.returned_requirements]
      exact List.Subset.refl _
    · intro child present
      apply TemplateScopeCovered.root selected.body.resources.graph_closed.rootsHaveNoParent
      rw [finalize_statementRoots selected.body.finalization]
      exact List.mem_map_of_mem present
    · intro child _
      exact ActualContext.covers_empty (.statement child)

theorem body_entry {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations) :
    ∃ target, BodyEntry selected target :=
  body_entry_of_interfaces selected checked (selected_original_interfaces selected member)

/-- The recursive assembly is applied at the real whole-body entry, with its
safe return type and state/context invariants discharged by accepted checking. -/
theorem body_of_recursive_of_interfaces {raw : Workspace.RawWorkspace}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces
      (checkingContext selected).signatures selected.body.finalized.solvedRequirements
      selected.body.finalized.typedSource)
    (sound : StatementsRootedSoundness selected fuel) :
    ∃ target, BodyEntry selected target ∧
      StatementsConclusion selected (checkingContext selected)
        (Ty.productMany selected.signature.returnTypes) selected.body.body [] target := by
  obtain ⟨target, entry⟩ := body_entry_of_interfaces selected checked interfaces
  exact ⟨target, entry, sound entry.returnSafe entry.returnAdmissible entry.boundary⟩

theorem body_of_recursive {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (member : row ∈ compiled.plan.specializations)
    (sound : StatementsRootedSoundness selected fuel) :
    ∃ target, BodyEntry selected target ∧
      StatementsConclusion selected (checkingContext selected)
        (Ty.productMany selected.signature.returnTypes) selected.body.body [] target :=
  body_of_recursive_of_interfaces selected checked
    (selected_original_interfaces selected member) sound

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
