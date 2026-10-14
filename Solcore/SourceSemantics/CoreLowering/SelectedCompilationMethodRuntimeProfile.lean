import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionTyping

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning
open CallablePreparedMethodRuntimeProfileFactory (SourceAt)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- The real retained method's declared callable type agrees with its raw input
binders before and after structural substitution. No packed arity is inverted. -/
theorem callable_shape {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : CallableCoercionBodyProvenance.Certificate program method)
    (valid : MethodDefinition.Valid program.signatures (MethodDefinition.ofChecked receipt.retained)) :
    method.specialized.function.type = .function
      (TypeSystem.Ty.productMany (method.specialized.function.typedBody.inputs.map (fun b => b.scheme.body)))
      method.specialized.function.inferredBodyType := by
  cases valid with
  | intro _ _ _ _ _ _ _ _ _ body =>
    cases body with
    | intro _ _ _ _ shape result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body) = _ at inputs
      have genericShape : receipt.retained.checked.type = .function
          (TypeSystem.Ty.productMany (receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body)))
          receipt.retained.checked.inferredBodyType := by
        rw [inputs]
        exact shape.trans (congrArg (TypeSystem.Ty.function _) result.symm)
      rw [receipt.result.2, genericShape]
      simp only [TypeSystem.ParameterSubstitution.apply]
      rw [← receipt.result.1, StructuralSubstitution.apply_productMany, receipt.inputs]
      simp only [List.map_map, Function.comp_def, StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, firstProjected, projected⟩ := bind_ok projected
    obtain ⟨rest, restProjected, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at restProjected
      subst rest
      exact firstProjected
    | cons next suffix =>
      have remaining := ih restProjected
      rw [List.mapM_cons] at restProjected
      obtain ⟨nextNative, _, restProjected⟩ := bind_ok restProjected
      obtain ⟨suffixNative, _, restProjected⟩ := bind_ok restProjected
      cases restProjected
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [firstProjected, remaining]
      rfl

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem parameters : (bodyInstance compiled.sourceProgram method).source.inputs = cached.named.inputs.map Prod.fst := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have fields := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted
  rw [← fields.1, cached.same] at fields
  exact fields.2.1.symm

theorem parameter_pack
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (valid : MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked receipt.retained)) :
    cached.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have shape := callable_shape receipt valid
  have inputs := parameters cached
  change method.specialized.function.typedBody.inputs = _ at inputs
  rw [inputs] at shape
  have actualShape : row.function.type = .function
      (TypeSystem.Ty.productMany (cached.named.inputs.map (fun b => b.1.scheme.body)))
      row.function.inferredBodyType := by
    rw [← same, cached.same]
    simpa only [List.map_map, Function.comp_def] using shape
  have projected := CompatibleExpressionReads.projectType_of_accepted
    (RecursiveNamedHeaderParameterProjections.prepared_parameter accepted actualShape)
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled cached.selected)
  exact Except.ok.inj (projected.symm.trans vector)

theorem source_at {values : SourceCoreCompatibleValues.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {context : SourceSemantics.Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements (bodyInstance compiled.sourceProgram method) dictionary)
    (unique : NodeOccurrencesUnique (bodyInstance compiled.sourceProgram method).source)
    (signatures : compiled.sourceProgram.signatures = values.checked.signatures) :
    Nonempty (SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary) := by
  obtain ⟨types, lexical, facts, typed, valid⟩ := SelectedCompilationMethodSelectionTyping.selected_typed selected
  have fields := RecursiveNamedInitialContextValidity.mono_fields typed.typing.inputs_extend
  refine ⟨⟨?_, parameters cached, cached.frame selected.selected, lexical, types, typed.typing.inputs_extend,
    ?_, fields.typeVariables.trans typed.type_variables_empty,
    fields.residualTypeVariables.trans typed.residual_type_variables_open,
    fields.signatures.trans (typed.signatures_eq.trans signatures), ?_, parameter_pack cached receipt (SelectedCompilationMethodSelectionTyping.retained_valid bodies cached receipt), unique⟩⟩
  · simp only [CallableIndexedNamedGeneration.source, cached.same, bodyInstance]
  · change CompatibleRuntimeContextValidity.Valid method.specialized.function.solvedRequirements lexical dictionary at valid
    simpa only [cached.same] using valid
  · rw [sameChecked]
    exact CallablePreparedMethodRuntimeProfileFactory.result_projection cached


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
