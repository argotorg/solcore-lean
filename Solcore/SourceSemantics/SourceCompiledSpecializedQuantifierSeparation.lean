import Solcore.SourceSemantics.SourceCompiledActualQuantifierSeparation

/-! Actual flexible finalization and rigid specialization preserve the owner
and quantified variables of every initialized local in a cached body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

/-- A specialized initialized binding is the actual finalization and parameter
application of an initialized binding in the same inferred body. -/
theorem BodySelection.specialized_initialized_origin
    (selected : BodySelection compiled named.specialized fuel)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings named.specialized.function.typedBody) :
    ∃ original ∈ initializedLetBindings (evidenceSource selected),
      current = StructuralSubstitution.applyInitializedLetBinding named.specialized.parameterSubstitution
        (FlexibleSubstitution.applyInitializedLetBinding selected.body.finalized.substitution original) ∧
      current.binder.scheme.quantified = original.binder.scheme.quantified ∧
      current.initializer = original.initializer := by
  rw [selected.source, selected.body.resources.source_eq] at member
  change current ∈ initializedLetBindings
    (StructuralSubstitution.applyTypedSource named.specialized.parameterSubstitution
      ((evidenceSource selected).applySubstitution selected.body.finalized.substitution)) at member
  rw [StructuralSubstitution.initializedLetBindings_applyTypedSource,
    FlexibleSubstitution.initializedLetBindings_applySubstitution] at member
  obtain ⟨finalized, finalMember, same⟩ := List.mem_map.mp member
  obtain ⟨original, originalMember, finalSame⟩ := List.mem_map.mp finalMember
  subst finalized
  subst current
  exact ⟨original, originalMember, rfl, rfl, rfl⟩

/-- Distinct owners in the authentic cached specialized source have disjoint
quantifiers. This uses the actual checker result and cache position. -/
theorem BodySelection.specialized_initialized_quantifiers_disjoint
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {current : InitializedLetBinding}
    (member : current ∈ initializedLetBindings named.specialized.function.typedBody) :
    ∀ other ∈ initializedLetBindings named.specialized.function.typedBody,
      other.binder ≠ current.binder →
      ∀ q ∈ current.binder.scheme.quantified, q ∉ other.binder.scheme.quantified := by
  obtain ⟨left, leftMember, leftEq, leftQuantified, _⟩ :=
    selected.specialized_initialized_origin member
  intro other otherMember different
  obtain ⟨right, rightMember, rightEq, rightQuantified, _⟩ :=
    selected.specialized_initialized_origin otherMember
  have rawDifferent : right.binder ≠ left.binder := by
    intro same
    apply different
    rw [rightEq, leftEq]
    change SourceSpecialization.applyBinder _ (right.binder.applySubstitution _) =
      SourceSpecialization.applyBinder _ (left.binder.applySubstitution _)
    rw [same]
  simpa only [leftQuantified, rightQuantified] using
    selected.initialized_quantifiers_disjoint artifact checked position leftMember
      right rightMember rawDifferent

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
