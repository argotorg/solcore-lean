import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts

/-! Actual named preparation and independent source signature typing determine
both ordered parameter vectors. Packed equality is proved from raw source shape
and real projection, then used only after source binder identity fixes arity.
Invocation evidence and exact source/native catalog identity remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderParameterProjections
open Core Frontend SourceInference RecursiveNamedCatalog

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- Only the outer function preparation is inverted. Its input fold is consumed
as the actual success witness and does not need to be exposed again. -/
theorem prepared_parameter {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    {parameter result : TypeSystem.Ty}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (shape : specialized.function.type = .function parameter result) :
    representation.expressions.projectType (.declaration specialized.key.declaration) parameter =
      .ok named.signature.parameterType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged, shape, pure, Except.pure, bind, Except.bind] at accepted
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, _, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact mapError_ok projected

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : SourceSemantics.Program}

theorem header_type (header : Header compiled.indexed.ancestry values definitions program)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    header.instantiation.type = .function
      (TypeSystem.Ty.productMany (header.bindings.map (fun binding => binding.1.scheme.body)))
      header.function.resultType := by
  obtain ⟨_, certificate⟩ := certified
  have types : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  rw [types, header.frame.result]
  exact certificate.callable_type

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
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

/-- The real prepared parameter projection agrees with the complete ordered
input vector, using independent source shape for the packed parameter type. -/
theorem parameter_pack (header : Header compiled.indexed.ancestry values definitions program)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    header.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd) := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have raw : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.named.inputs.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binders
  have shape := matched.type.trans (header_type header certified)
  rw [raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled header.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape := same ▸ shape
  have projected := prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany (RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)

/-- The Header's native projection callback is now supplied by actual compiler
receipts; the source and compiler catalogs must still be the same catalog. -/
theorem projections (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (matched : CallableNamedMetadata.Matches header.named.specialized header.instantiation) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := by
  apply RecursiveNamedParameterPackingFacts.header_projections header (parameter_pack header certified matched)
  rw [sameChecked]
  exact RecursiveNamedPreparedParameterProjections.cached_projected compiled header.selected

/-- Complete exact plan selection supplies the metadata match without a
separate Matches assumption. A key alone is deliberately insufficient. -/
theorem projections_of_record (header : Header compiled.indexed.ancestry values definitions program)
    (sameChecked : values.checked = compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) :=
  projections header sameChecked certified (CallableNamedMetadata.matches_of_exact header.target record)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderParameterProjections
